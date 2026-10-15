import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_linear.container_with_most_water_linear_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_linear.container_with_most_water_linear_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance container_with_most_water_linear_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def maxAreaLinear_safety_wit_1 : Prop :=
  forall (heightSize_pre : Int) (height_pre : Int) (l : (List Int)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : (height_pre ≠ (0 : Int))) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "maximumArea" ) )) # Int |->_)
  ** ((( &( "right" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** (intArray.full height_pre heightSize_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def maxAreaLinear_safety_wit_2 : Prop :=
  forall (heightSize_pre : Int) (height_pre : Int) (l : (List Int)) (PreH1 : (height_pre = (0 : Int))) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : (height_pre ≠ (0 : Int))) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH7 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "maximumArea" ) )) # Int |->_)
  ** ((( &( "right" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** (intArray.full height_pre heightSize_pre l)
|--
  “ False ”

noncomputable def maxAreaLinear_safety_wit_3 : Prop :=
  forall (heightSize_pre : Int) (height_pre : Int) (l : (List Int)) (PreH1 : (height_pre ≠ (0 : Int))) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : (height_pre ≠ (0 : Int))) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH7 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "maximumArea" ) )) # Int |->_)
  ** ((( &( "right" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** (intArray.full height_pre heightSize_pre l)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def maxAreaLinear_safety_wit_4 : Prop :=
  forall (heightSize_pre : Int) (height_pre : Int) (l : (List Int)) (PreH1 : (heightSize_pre < 2)) (PreH2 : (height_pre ≠ (0 : Int))) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : (height_pre ≠ (0 : Int))) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH8 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "maximumArea" ) )) # Int |->_)
  ** ((( &( "right" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** (intArray.full height_pre heightSize_pre l)
|--
  “ False ”

noncomputable def maxAreaLinear_safety_wit_5 : Prop :=
  forall (heightSize_pre : Int) (height_pre : Int) (l : (List Int)) (PreH1 : (heightSize_pre >= 2)) (PreH2 : (height_pre ≠ (0 : Int))) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : (height_pre ≠ (0 : Int))) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH8 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "maximumArea" ) )) # Int |->_)
  ** ((( &( "right" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** (intArray.full height_pre heightSize_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def maxAreaLinear_safety_wit_6 : Prop :=
  forall (heightSize_pre : Int) (height_pre : Int) (l : (List Int)) (PreH1 : (heightSize_pre >= 2)) (PreH2 : (height_pre ≠ (0 : Int))) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : (height_pre ≠ (0 : Int))) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH8 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "maximumArea" ) )) # Int |->_)
  ** ((( &( "right" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** (intArray.full height_pre heightSize_pre l)
|--
  “ ((heightSize_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (heightSize_pre - 1)) ”

noncomputable def maxAreaLinear_safety_wit_7 : Prop :=
  forall (heightSize_pre : Int) (height_pre : Int) (l : (List Int)) (PreH1 : (heightSize_pre >= 2)) (PreH2 : (height_pre ≠ (0 : Int))) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : (height_pre ≠ (0 : Int))) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH8 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "maximumArea" ) )) # Int |->_)
  ** ((( &( "right" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** (intArray.full height_pre heightSize_pre l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def maxAreaLinear_safety_wit_8 : Prop :=
  forall (heightSize_pre : Int) (height_pre : Int) (l : (List Int)) (PreH1 : (heightSize_pre >= 2)) (PreH2 : (height_pre ≠ (0 : Int))) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : (height_pre ≠ (0 : Int))) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH8 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "maximumArea" ) )) # Int |->_)
  ** ((( &( "right" ) )) # Int |-> ((heightSize_pre - 1)))
  ** ((( &( "left" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** (intArray.full height_pre heightSize_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def maxAreaLinear_safety_wit_9 : Prop :=
  forall (heightSize_pre : Int) (height_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : (left < right)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : (left <= right)) (PreH7 : (right < heightSize_pre)) (PreH8 : ((0 : Int) <= maximumArea)) (PreH9 : (maximumArea <= 999990000)) (PreH10 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "width" ) )) # Int |->_)
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
  ** (intArray.full height_pre heightSize_pre l)
|--
  “ ((right - left) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (right - left)) ”

noncomputable def maxAreaLinear_safety_wit_10 : Prop :=
  (
forall (heightSize_pre : Int) (height_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : ((Znth left l (0 : Int)) < (Znth right l (0 : Int)))) (PreH2 : (left < right)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : (left <= right)) (PreH8 : (right < heightSize_pre)) (PreH9 : ((0 : Int) <= maximumArea)) (PreH10 : (maximumArea <= 999990000)) (PreH11 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH13 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** ((( &( "area" ) )) # Int |->_)
  ** ((( &( "shorterHeight" ) )) # Int |-> ((Znth left l (0 : Int))))
  ** ((( &( "width" ) )) # Int |-> ((right - left)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
|--
  “ (((right - left) * (Znth left l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((right - left) * (Znth left l (0 : Int)))) ”
) \/
(
forall (heightSize_pre : Int) (height_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : ((Znth left l (0 : Int)) < (Znth right l (0 : Int)))) (PreH2 : (left < right)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : (left <= right)) (PreH8 : (right < heightSize_pre)) (PreH9 : ((0 : Int) <= maximumArea)) (PreH10 : (maximumArea <= 999990000)) (PreH11 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH13 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** ((( &( "area" ) )) # Int |->_)
  ** ((( &( "shorterHeight" ) )) # Int |-> ((Znth left l (0 : Int))))
  ** ((( &( "width" ) )) # Int |-> ((right - left)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
|--
  “ (((right - left) * (Znth left l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((right - left) * (Znth left l (0 : Int)))) ”
)

noncomputable def maxAreaLinear_safety_wit_10_split_goal_1 : Prop :=
  forall (heightSize_pre : Int) (height_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : ((Znth left l (0 : Int)) < (Znth right l (0 : Int)))) (PreH2 : (left < right)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : (left <= right)) (PreH8 : (right < heightSize_pre)) (PreH9 : ((0 : Int) <= maximumArea)) (PreH10 : (maximumArea <= 999990000)) (PreH11 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH13 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** ((( &( "area" ) )) # Int |->_)
  ** ((( &( "shorterHeight" ) )) # Int |-> ((Znth left l (0 : Int))))
  ** ((( &( "width" ) )) # Int |-> ((right - left)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
|--
  “ (((right - left) * (Znth left l (0 : Int))) <= INT_MAX) ”

noncomputable def maxAreaLinear_safety_wit_10_split_goal_2 : Prop :=
  forall (heightSize_pre : Int) (height_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : ((Znth left l (0 : Int)) < (Znth right l (0 : Int)))) (PreH2 : (left < right)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : (left <= right)) (PreH8 : (right < heightSize_pre)) (PreH9 : ((0 : Int) <= maximumArea)) (PreH10 : (maximumArea <= 999990000)) (PreH11 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH13 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** ((( &( "area" ) )) # Int |->_)
  ** ((( &( "shorterHeight" ) )) # Int |-> ((Znth left l (0 : Int))))
  ** ((( &( "width" ) )) # Int |-> ((right - left)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
|--
  “ ((INT_MIN) <= ((right - left) * (Znth left l (0 : Int)))) ”

noncomputable def maxAreaLinear_safety_wit_11 : Prop :=
  (
forall (heightSize_pre : Int) (height_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : ((Znth left l (0 : Int)) >= (Znth right l (0 : Int)))) (PreH2 : (left < right)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : (left <= right)) (PreH8 : (right < heightSize_pre)) (PreH9 : ((0 : Int) <= maximumArea)) (PreH10 : (maximumArea <= 999990000)) (PreH11 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH13 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** ((( &( "area" ) )) # Int |->_)
  ** ((( &( "shorterHeight" ) )) # Int |-> ((Znth right l (0 : Int))))
  ** ((( &( "width" ) )) # Int |-> ((right - left)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
|--
  “ (((right - left) * (Znth right l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((right - left) * (Znth right l (0 : Int)))) ”
) \/
(
forall (heightSize_pre : Int) (height_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : ((Znth left l (0 : Int)) >= (Znth right l (0 : Int)))) (PreH2 : (left < right)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : (left <= right)) (PreH8 : (right < heightSize_pre)) (PreH9 : ((0 : Int) <= maximumArea)) (PreH10 : (maximumArea <= 999990000)) (PreH11 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH13 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** ((( &( "area" ) )) # Int |->_)
  ** ((( &( "shorterHeight" ) )) # Int |-> ((Znth right l (0 : Int))))
  ** ((( &( "width" ) )) # Int |-> ((right - left)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
|--
  “ (((right - left) * (Znth right l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((right - left) * (Znth right l (0 : Int)))) ”
)

noncomputable def maxAreaLinear_safety_wit_11_split_goal_1 : Prop :=
  forall (heightSize_pre : Int) (height_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : ((Znth left l (0 : Int)) >= (Znth right l (0 : Int)))) (PreH2 : (left < right)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : (left <= right)) (PreH8 : (right < heightSize_pre)) (PreH9 : ((0 : Int) <= maximumArea)) (PreH10 : (maximumArea <= 999990000)) (PreH11 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH13 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** ((( &( "area" ) )) # Int |->_)
  ** ((( &( "shorterHeight" ) )) # Int |-> ((Znth right l (0 : Int))))
  ** ((( &( "width" ) )) # Int |-> ((right - left)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
|--
  “ (((right - left) * (Znth right l (0 : Int))) <= INT_MAX) ”

noncomputable def maxAreaLinear_safety_wit_11_split_goal_2 : Prop :=
  forall (heightSize_pre : Int) (height_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : ((Znth left l (0 : Int)) >= (Znth right l (0 : Int)))) (PreH2 : (left < right)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : (left <= right)) (PreH8 : (right < heightSize_pre)) (PreH9 : ((0 : Int) <= maximumArea)) (PreH10 : (maximumArea <= 999990000)) (PreH11 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH13 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** ((( &( "area" ) )) # Int |->_)
  ** ((( &( "shorterHeight" ) )) # Int |-> ((Znth right l (0 : Int))))
  ** ((( &( "width" ) )) # Int |-> ((right - left)))
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
|--
  “ ((INT_MIN) <= ((right - left) * (Znth right l (0 : Int)))) ”

noncomputable def maxAreaLinear_safety_wit_12 : Prop :=
  forall (heightSize_pre : Int) (height_pre : Int) (l : (List Int)) (left : Int) (right : Int) (width : Int) (shorterHeight : Int) (area : Int) (maximumArea : Int) (PreH1 : ((Znth left l (0 : Int)) < (Znth right l (0 : Int)))) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : (left < right)) (PreH7 : (right < heightSize_pre)) (PreH8 : (width = (right - left))) (PreH9 : (1 <= width)) (PreH10 : (width <= 99999)) (PreH11 : (shorterHeight = (LinearContainerHeight (l) (left) (right)))) (PreH12 : ((0 : Int) <= shorterHeight)) (PreH13 : (shorterHeight <= 10000)) (PreH14 : (area = (LinearContainerArea (l) (left) (right)))) (PreH15 : ((0 : Int) <= area)) (PreH16 : (area <= maximumArea)) (PreH17 : ((0 : Int) <= maximumArea)) (PreH18 : (maximumArea <= 999990000)) (PreH19 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "shorterHeight" ) )) # Int |-> (shorterHeight))
  ** ((( &( "area" ) )) # Int |-> (area))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
|--
  “ ((left + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left + 1)) ”

noncomputable def maxAreaLinear_safety_wit_13 : Prop :=
  forall (heightSize_pre : Int) (height_pre : Int) (l : (List Int)) (left : Int) (right : Int) (width : Int) (shorterHeight : Int) (area : Int) (maximumArea : Int) (PreH1 : ((Znth left l (0 : Int)) >= (Znth right l (0 : Int)))) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : (left < right)) (PreH7 : (right < heightSize_pre)) (PreH8 : (width = (right - left))) (PreH9 : (1 <= width)) (PreH10 : (width <= 99999)) (PreH11 : (shorterHeight = (LinearContainerHeight (l) (left) (right)))) (PreH12 : ((0 : Int) <= shorterHeight)) (PreH13 : (shorterHeight <= 10000)) (PreH14 : (area = (LinearContainerArea (l) (left) (right)))) (PreH15 : ((0 : Int) <= area)) (PreH16 : (area <= maximumArea)) (PreH17 : ((0 : Int) <= maximumArea)) (PreH18 : (maximumArea <= 999990000)) (PreH19 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
  ** ((( &( "height" ) )) # Ptr |-> (height_pre))
  ** ((( &( "heightSize" ) )) # Int |-> (heightSize_pre))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "shorterHeight" ) )) # Int |-> (shorterHeight))
  ** ((( &( "area" ) )) # Int |-> (area))
  ** ((( &( "maximumArea" ) )) # Int |-> (maximumArea))
|--
  “ ((right - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (right - 1)) ”

noncomputable def maxAreaLinear_entail_wit_1 : Prop :=
  (
forall (heightSize_pre : Int) (height_pre : Int) (l : (List Int)) (PreH1 : (heightSize_pre >= 2)) (PreH2 : (height_pre ≠ (0 : Int))) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : (height_pre ≠ (0 : Int))) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH8 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
|--
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (heightSize_pre - 1)) ” &&
  “ ((heightSize_pre - 1) < heightSize_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 999990000) ” &&
  “ (LinearContainerTwoPointerInvariant l (0 : Int) (heightSize_pre - 1) (0 : Int)) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
) \/
(
forall (heightSize_pre : Int) (height_pre : Int) (l : (List Int)) (PreH1 : (heightSize_pre >= 2)) (PreH2 : (height_pre ≠ (0 : Int))) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : (height_pre ≠ (0 : Int))) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH8 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ (LinearContainerTwoPointerInvariant l (0 : Int) (heightSize_pre - 1) (0 : Int)) ”
  &&  emp
)

noncomputable def maxAreaLinear_entail_wit_1_split_goal_1 : Prop :=
  forall (heightSize_pre : Int) (height_pre : Int) (l : (List Int)) (PreH1 : (heightSize_pre >= 2)) (PreH2 : (height_pre ≠ (0 : Int))) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : (height_pre ≠ (0 : Int))) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH8 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (LinearContainerTwoPointerInvariant l (0 : Int) (heightSize_pre - 1) (0 : Int))

noncomputable def maxAreaLinear_entail_wit_2_1 : Prop :=
  (
forall (heightSize_pre : Int) (height_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : (((right - left) * (Znth left l (0 : Int))) > maximumArea)) (PreH2 : ((Znth left l (0 : Int)) < (Znth right l (0 : Int)))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
|--
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < right) ” &&
  “ (right < heightSize_pre) ” &&
  “ ((right - left) = (right - left)) ” &&
  “ (1 <= (right - left)) ” &&
  “ ((right - left) <= 99999) ” &&
  “ ((Znth left l (0 : Int)) = (LinearContainerHeight (l) (left) (right))) ” &&
  “ ((0 : Int) <= (Znth left l (0 : Int))) ” &&
  “ ((Znth left l (0 : Int)) <= 10000) ” &&
  “ (((right - left) * (Znth left l (0 : Int))) = (LinearContainerArea (l) (left) (right))) ” &&
  “ ((0 : Int) <= ((right - left) * (Znth left l (0 : Int)))) ” &&
  “ (((right - left) * (Znth left l (0 : Int))) <= ((right - left) * (Znth left l (0 : Int)))) ” &&
  “ ((0 : Int) <= ((right - left) * (Znth left l (0 : Int)))) ” &&
  “ (((right - left) * (Znth left l (0 : Int))) <= 999990000) ” &&
  “ (LinearContainerTwoPointerInvariant l left right ((right - left) * (Znth left l (0 : Int)))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
) \/
(
forall (heightSize_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : (((right - left) * (Znth left l (0 : Int))) > maximumArea)) (PreH2 : ((Znth left l (0 : Int)) < (Znth right l (0 : Int)))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ (LinearContainerTwoPointerInvariant l left right ((right - left) * (Znth left l (0 : Int)))) ” &&
  “ (((right - left) * (Znth left l (0 : Int))) <= 999990000) ” &&
  “ (((right - left) * (Znth left l (0 : Int))) = (LinearContainerArea (l) (left) (right))) ” &&
  “ ((Znth left l (0 : Int)) <= 10000) ” &&
  “ ((0 : Int) <= (Znth left l (0 : Int))) ” &&
  “ ((Znth left l (0 : Int)) = (LinearContainerHeight (l) (left) (right))) ”
  &&  emp
)

noncomputable def maxAreaLinear_entail_wit_2_1_split_goal_1 : Prop :=
  forall (heightSize_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : (((right - left) * (Znth left l (0 : Int))) > maximumArea)) (PreH2 : ((Znth left l (0 : Int)) < (Znth right l (0 : Int)))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (LinearContainerTwoPointerInvariant l left right ((right - left) * (Znth left l (0 : Int))))

noncomputable def maxAreaLinear_entail_wit_2_1_split_goal_2 : Prop :=
  forall (heightSize_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : (((right - left) * (Znth left l (0 : Int))) > maximumArea)) (PreH2 : ((Znth left l (0 : Int)) < (Znth right l (0 : Int)))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (((right - left) * (Znth left l (0 : Int))) <= 999990000)

noncomputable def maxAreaLinear_entail_wit_2_1_split_goal_3 : Prop :=
  forall (heightSize_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : (((right - left) * (Znth left l (0 : Int))) > maximumArea)) (PreH2 : ((Znth left l (0 : Int)) < (Znth right l (0 : Int)))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (((right - left) * (Znth left l (0 : Int))) = (LinearContainerArea (l) (left) (right)))

noncomputable def maxAreaLinear_entail_wit_2_1_split_goal_4 : Prop :=
  forall (heightSize_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : (((right - left) * (Znth left l (0 : Int))) > maximumArea)) (PreH2 : ((Znth left l (0 : Int)) < (Znth right l (0 : Int)))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((Znth left l (0 : Int)) <= 10000)

noncomputable def maxAreaLinear_entail_wit_2_1_split_goal_5 : Prop :=
  forall (heightSize_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : (((right - left) * (Znth left l (0 : Int))) > maximumArea)) (PreH2 : ((Znth left l (0 : Int)) < (Znth right l (0 : Int)))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((0 : Int) <= (Znth left l (0 : Int)))

noncomputable def maxAreaLinear_entail_wit_2_1_split_goal_6 : Prop :=
  forall (heightSize_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : (((right - left) * (Znth left l (0 : Int))) > maximumArea)) (PreH2 : ((Znth left l (0 : Int)) < (Znth right l (0 : Int)))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((Znth left l (0 : Int)) = (LinearContainerHeight (l) (left) (right)))

noncomputable def maxAreaLinear_entail_wit_2_2 : Prop :=
  (
forall (heightSize_pre : Int) (height_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : (((right - left) * (Znth right l (0 : Int))) > maximumArea)) (PreH2 : ((Znth left l (0 : Int)) >= (Znth right l (0 : Int)))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
|--
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < right) ” &&
  “ (right < heightSize_pre) ” &&
  “ ((right - left) = (right - left)) ” &&
  “ (1 <= (right - left)) ” &&
  “ ((right - left) <= 99999) ” &&
  “ ((Znth right l (0 : Int)) = (LinearContainerHeight (l) (left) (right))) ” &&
  “ ((0 : Int) <= (Znth right l (0 : Int))) ” &&
  “ ((Znth right l (0 : Int)) <= 10000) ” &&
  “ (((right - left) * (Znth right l (0 : Int))) = (LinearContainerArea (l) (left) (right))) ” &&
  “ ((0 : Int) <= ((right - left) * (Znth right l (0 : Int)))) ” &&
  “ (((right - left) * (Znth right l (0 : Int))) <= ((right - left) * (Znth right l (0 : Int)))) ” &&
  “ ((0 : Int) <= ((right - left) * (Znth right l (0 : Int)))) ” &&
  “ (((right - left) * (Znth right l (0 : Int))) <= 999990000) ” &&
  “ (LinearContainerTwoPointerInvariant l left right ((right - left) * (Znth right l (0 : Int)))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
) \/
(
forall (heightSize_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : (((right - left) * (Znth right l (0 : Int))) > maximumArea)) (PreH2 : ((Znth left l (0 : Int)) >= (Znth right l (0 : Int)))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ (LinearContainerTwoPointerInvariant l left right ((right - left) * (Znth right l (0 : Int)))) ” &&
  “ (((right - left) * (Znth right l (0 : Int))) <= 999990000) ” &&
  “ (((right - left) * (Znth right l (0 : Int))) = (LinearContainerArea (l) (left) (right))) ” &&
  “ ((Znth right l (0 : Int)) <= 10000) ” &&
  “ ((0 : Int) <= (Znth right l (0 : Int))) ” &&
  “ ((Znth right l (0 : Int)) = (LinearContainerHeight (l) (left) (right))) ”
  &&  emp
)

noncomputable def maxAreaLinear_entail_wit_2_2_split_goal_1 : Prop :=
  forall (heightSize_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : (((right - left) * (Znth right l (0 : Int))) > maximumArea)) (PreH2 : ((Znth left l (0 : Int)) >= (Znth right l (0 : Int)))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (LinearContainerTwoPointerInvariant l left right ((right - left) * (Znth right l (0 : Int))))

noncomputable def maxAreaLinear_entail_wit_2_2_split_goal_2 : Prop :=
  forall (heightSize_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : (((right - left) * (Znth right l (0 : Int))) > maximumArea)) (PreH2 : ((Znth left l (0 : Int)) >= (Znth right l (0 : Int)))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (((right - left) * (Znth right l (0 : Int))) <= 999990000)

noncomputable def maxAreaLinear_entail_wit_2_2_split_goal_3 : Prop :=
  forall (heightSize_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : (((right - left) * (Znth right l (0 : Int))) > maximumArea)) (PreH2 : ((Znth left l (0 : Int)) >= (Znth right l (0 : Int)))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (((right - left) * (Znth right l (0 : Int))) = (LinearContainerArea (l) (left) (right)))

noncomputable def maxAreaLinear_entail_wit_2_2_split_goal_4 : Prop :=
  forall (heightSize_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : (((right - left) * (Znth right l (0 : Int))) > maximumArea)) (PreH2 : ((Znth left l (0 : Int)) >= (Znth right l (0 : Int)))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((Znth right l (0 : Int)) <= 10000)

noncomputable def maxAreaLinear_entail_wit_2_2_split_goal_5 : Prop :=
  forall (heightSize_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : (((right - left) * (Znth right l (0 : Int))) > maximumArea)) (PreH2 : ((Znth left l (0 : Int)) >= (Znth right l (0 : Int)))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((0 : Int) <= (Znth right l (0 : Int)))

noncomputable def maxAreaLinear_entail_wit_2_2_split_goal_6 : Prop :=
  forall (heightSize_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : (((right - left) * (Znth right l (0 : Int))) > maximumArea)) (PreH2 : ((Znth left l (0 : Int)) >= (Znth right l (0 : Int)))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((Znth right l (0 : Int)) = (LinearContainerHeight (l) (left) (right)))

noncomputable def maxAreaLinear_entail_wit_2_3 : Prop :=
  (
forall (heightSize_pre : Int) (height_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : (((right - left) * (Znth left l (0 : Int))) <= maximumArea)) (PreH2 : ((Znth left l (0 : Int)) < (Znth right l (0 : Int)))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
|--
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < right) ” &&
  “ (right < heightSize_pre) ” &&
  “ ((right - left) = (right - left)) ” &&
  “ (1 <= (right - left)) ” &&
  “ ((right - left) <= 99999) ” &&
  “ ((Znth left l (0 : Int)) = (LinearContainerHeight (l) (left) (right))) ” &&
  “ ((0 : Int) <= (Znth left l (0 : Int))) ” &&
  “ ((Znth left l (0 : Int)) <= 10000) ” &&
  “ (((right - left) * (Znth left l (0 : Int))) = (LinearContainerArea (l) (left) (right))) ” &&
  “ ((0 : Int) <= ((right - left) * (Znth left l (0 : Int)))) ” &&
  “ (((right - left) * (Znth left l (0 : Int))) <= maximumArea) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (LinearContainerTwoPointerInvariant l left right maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
) \/
(
forall (heightSize_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : (((right - left) * (Znth left l (0 : Int))) <= maximumArea)) (PreH2 : ((Znth left l (0 : Int)) < (Znth right l (0 : Int)))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ ((0 : Int) <= ((right - left) * (Znth left l (0 : Int)))) ” &&
  “ (((right - left) * (Znth left l (0 : Int))) = (LinearContainerArea (l) (left) (right))) ” &&
  “ ((Znth left l (0 : Int)) <= 10000) ” &&
  “ ((0 : Int) <= (Znth left l (0 : Int))) ” &&
  “ ((Znth left l (0 : Int)) = (LinearContainerHeight (l) (left) (right))) ”
  &&  emp
)

noncomputable def maxAreaLinear_entail_wit_2_3_split_goal_1 : Prop :=
  forall (heightSize_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : (((right - left) * (Znth left l (0 : Int))) <= maximumArea)) (PreH2 : ((Znth left l (0 : Int)) < (Znth right l (0 : Int)))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((0 : Int) <= ((right - left) * (Znth left l (0 : Int))))

noncomputable def maxAreaLinear_entail_wit_2_3_split_goal_2 : Prop :=
  forall (heightSize_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : (((right - left) * (Znth left l (0 : Int))) <= maximumArea)) (PreH2 : ((Znth left l (0 : Int)) < (Znth right l (0 : Int)))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (((right - left) * (Znth left l (0 : Int))) = (LinearContainerArea (l) (left) (right)))

noncomputable def maxAreaLinear_entail_wit_2_3_split_goal_3 : Prop :=
  forall (heightSize_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : (((right - left) * (Znth left l (0 : Int))) <= maximumArea)) (PreH2 : ((Znth left l (0 : Int)) < (Znth right l (0 : Int)))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((Znth left l (0 : Int)) <= 10000)

noncomputable def maxAreaLinear_entail_wit_2_3_split_goal_4 : Prop :=
  forall (heightSize_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : (((right - left) * (Znth left l (0 : Int))) <= maximumArea)) (PreH2 : ((Znth left l (0 : Int)) < (Znth right l (0 : Int)))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((0 : Int) <= (Znth left l (0 : Int)))

noncomputable def maxAreaLinear_entail_wit_2_3_split_goal_5 : Prop :=
  forall (heightSize_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : (((right - left) * (Znth left l (0 : Int))) <= maximumArea)) (PreH2 : ((Znth left l (0 : Int)) < (Znth right l (0 : Int)))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((Znth left l (0 : Int)) = (LinearContainerHeight (l) (left) (right)))

noncomputable def maxAreaLinear_entail_wit_2_4 : Prop :=
  (
forall (heightSize_pre : Int) (height_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : (((right - left) * (Znth right l (0 : Int))) <= maximumArea)) (PreH2 : ((Znth left l (0 : Int)) >= (Znth right l (0 : Int)))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
|--
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < right) ” &&
  “ (right < heightSize_pre) ” &&
  “ ((right - left) = (right - left)) ” &&
  “ (1 <= (right - left)) ” &&
  “ ((right - left) <= 99999) ” &&
  “ ((Znth right l (0 : Int)) = (LinearContainerHeight (l) (left) (right))) ” &&
  “ ((0 : Int) <= (Znth right l (0 : Int))) ” &&
  “ ((Znth right l (0 : Int)) <= 10000) ” &&
  “ (((right - left) * (Znth right l (0 : Int))) = (LinearContainerArea (l) (left) (right))) ” &&
  “ ((0 : Int) <= ((right - left) * (Znth right l (0 : Int)))) ” &&
  “ (((right - left) * (Znth right l (0 : Int))) <= maximumArea) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (LinearContainerTwoPointerInvariant l left right maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
) \/
(
forall (heightSize_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : (((right - left) * (Znth right l (0 : Int))) <= maximumArea)) (PreH2 : ((Znth left l (0 : Int)) >= (Znth right l (0 : Int)))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ ((0 : Int) <= ((right - left) * (Znth right l (0 : Int)))) ” &&
  “ (((right - left) * (Znth right l (0 : Int))) = (LinearContainerArea (l) (left) (right))) ” &&
  “ ((Znth right l (0 : Int)) <= 10000) ” &&
  “ ((0 : Int) <= (Znth right l (0 : Int))) ” &&
  “ ((Znth right l (0 : Int)) = (LinearContainerHeight (l) (left) (right))) ”
  &&  emp
)

noncomputable def maxAreaLinear_entail_wit_2_4_split_goal_1 : Prop :=
  forall (heightSize_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : (((right - left) * (Znth right l (0 : Int))) <= maximumArea)) (PreH2 : ((Znth left l (0 : Int)) >= (Znth right l (0 : Int)))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((0 : Int) <= ((right - left) * (Znth right l (0 : Int))))

noncomputable def maxAreaLinear_entail_wit_2_4_split_goal_2 : Prop :=
  forall (heightSize_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : (((right - left) * (Znth right l (0 : Int))) <= maximumArea)) (PreH2 : ((Znth left l (0 : Int)) >= (Znth right l (0 : Int)))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (((right - left) * (Znth right l (0 : Int))) = (LinearContainerArea (l) (left) (right)))

noncomputable def maxAreaLinear_entail_wit_2_4_split_goal_3 : Prop :=
  forall (heightSize_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : (((right - left) * (Znth right l (0 : Int))) <= maximumArea)) (PreH2 : ((Znth left l (0 : Int)) >= (Znth right l (0 : Int)))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((Znth right l (0 : Int)) <= 10000)

noncomputable def maxAreaLinear_entail_wit_2_4_split_goal_4 : Prop :=
  forall (heightSize_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : (((right - left) * (Znth right l (0 : Int))) <= maximumArea)) (PreH2 : ((Znth left l (0 : Int)) >= (Znth right l (0 : Int)))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((0 : Int) <= (Znth right l (0 : Int)))

noncomputable def maxAreaLinear_entail_wit_2_4_split_goal_5 : Prop :=
  forall (heightSize_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : (((right - left) * (Znth right l (0 : Int))) <= maximumArea)) (PreH2 : ((Znth left l (0 : Int)) >= (Znth right l (0 : Int)))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : ((0 : Int) <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((Znth right l (0 : Int)) = (LinearContainerHeight (l) (left) (right)))

noncomputable def maxAreaLinear_entail_wit_3_1 : Prop :=
  (
forall (heightSize_pre : Int) (height_pre : Int) (l : (List Int)) (left : Int) (right : Int) (width : Int) (shorterHeight : Int) (area : Int) (maximumArea : Int) (PreH1 : ((Znth left l (0 : Int)) < (Znth right l (0 : Int)))) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : (left < right)) (PreH7 : (right < heightSize_pre)) (PreH8 : (width = (right - left))) (PreH9 : (1 <= width)) (PreH10 : (width <= 99999)) (PreH11 : (shorterHeight = (LinearContainerHeight (l) (left) (right)))) (PreH12 : ((0 : Int) <= shorterHeight)) (PreH13 : (shorterHeight <= 10000)) (PreH14 : (area = (LinearContainerArea (l) (left) (right)))) (PreH15 : ((0 : Int) <= area)) (PreH16 : (area <= maximumArea)) (PreH17 : ((0 : Int) <= maximumArea)) (PreH18 : (maximumArea <= 999990000)) (PreH19 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
|--
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ ((0 : Int) <= (left + 1)) ” &&
  “ ((left + 1) <= right) ” &&
  “ (right < heightSize_pre) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (LinearContainerTwoPointerInvariant l (left + 1) right maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
) \/
(
forall (heightSize_pre : Int) (l : (List Int)) (left : Int) (right : Int) (width : Int) (shorterHeight : Int) (area : Int) (maximumArea : Int) (PreH1 : ((Znth left l (0 : Int)) < (Znth right l (0 : Int)))) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : (left < right)) (PreH7 : (right < heightSize_pre)) (PreH8 : (width = (right - left))) (PreH9 : (1 <= width)) (PreH10 : (width <= 99999)) (PreH11 : (shorterHeight = (LinearContainerHeight (l) (left) (right)))) (PreH12 : ((0 : Int) <= shorterHeight)) (PreH13 : (shorterHeight <= 10000)) (PreH14 : (area = (LinearContainerArea (l) (left) (right)))) (PreH15 : ((0 : Int) <= area)) (PreH16 : (area <= maximumArea)) (PreH17 : ((0 : Int) <= maximumArea)) (PreH18 : (maximumArea <= 999990000)) (PreH19 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ (LinearContainerTwoPointerInvariant l (left + 1) right maximumArea) ”
  &&  emp
)

noncomputable def maxAreaLinear_entail_wit_3_1_split_goal_1 : Prop :=
  forall (heightSize_pre : Int) (l : (List Int)) (left : Int) (right : Int) (width : Int) (shorterHeight : Int) (area : Int) (maximumArea : Int) (PreH1 : ((Znth left l (0 : Int)) < (Znth right l (0 : Int)))) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : (left < right)) (PreH7 : (right < heightSize_pre)) (PreH8 : (width = (right - left))) (PreH9 : (1 <= width)) (PreH10 : (width <= 99999)) (PreH11 : (shorterHeight = (LinearContainerHeight (l) (left) (right)))) (PreH12 : ((0 : Int) <= shorterHeight)) (PreH13 : (shorterHeight <= 10000)) (PreH14 : (area = (LinearContainerArea (l) (left) (right)))) (PreH15 : ((0 : Int) <= area)) (PreH16 : (area <= maximumArea)) (PreH17 : ((0 : Int) <= maximumArea)) (PreH18 : (maximumArea <= 999990000)) (PreH19 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (LinearContainerTwoPointerInvariant l (left + 1) right maximumArea)

noncomputable def maxAreaLinear_entail_wit_3_2 : Prop :=
  (
forall (heightSize_pre : Int) (height_pre : Int) (l : (List Int)) (left : Int) (right : Int) (width : Int) (shorterHeight : Int) (area : Int) (maximumArea : Int) (PreH1 : ((Znth left l (0 : Int)) >= (Znth right l (0 : Int)))) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : (left < right)) (PreH7 : (right < heightSize_pre)) (PreH8 : (width = (right - left))) (PreH9 : (1 <= width)) (PreH10 : (width <= 99999)) (PreH11 : (shorterHeight = (LinearContainerHeight (l) (left) (right)))) (PreH12 : ((0 : Int) <= shorterHeight)) (PreH13 : (shorterHeight <= 10000)) (PreH14 : (area = (LinearContainerArea (l) (left) (right)))) (PreH15 : ((0 : Int) <= area)) (PreH16 : (area <= maximumArea)) (PreH17 : ((0 : Int) <= maximumArea)) (PreH18 : (maximumArea <= 999990000)) (PreH19 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
|--
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left <= (right - 1)) ” &&
  “ ((right - 1) < heightSize_pre) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (LinearContainerTwoPointerInvariant l left (right - 1) maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full height_pre heightSize_pre l)
) \/
(
forall (heightSize_pre : Int) (l : (List Int)) (left : Int) (right : Int) (width : Int) (shorterHeight : Int) (area : Int) (maximumArea : Int) (PreH1 : ((Znth left l (0 : Int)) >= (Znth right l (0 : Int)))) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : (left < right)) (PreH7 : (right < heightSize_pre)) (PreH8 : (width = (right - left))) (PreH9 : (1 <= width)) (PreH10 : (width <= 99999)) (PreH11 : (shorterHeight = (LinearContainerHeight (l) (left) (right)))) (PreH12 : ((0 : Int) <= shorterHeight)) (PreH13 : (shorterHeight <= 10000)) (PreH14 : (area = (LinearContainerArea (l) (left) (right)))) (PreH15 : ((0 : Int) <= area)) (PreH16 : (area <= maximumArea)) (PreH17 : ((0 : Int) <= maximumArea)) (PreH18 : (maximumArea <= 999990000)) (PreH19 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ (LinearContainerTwoPointerInvariant l left (right - 1) maximumArea) ”
  &&  emp
)

noncomputable def maxAreaLinear_entail_wit_3_2_split_goal_1 : Prop :=
  forall (heightSize_pre : Int) (l : (List Int)) (left : Int) (right : Int) (width : Int) (shorterHeight : Int) (area : Int) (maximumArea : Int) (PreH1 : ((Znth left l (0 : Int)) >= (Znth right l (0 : Int)))) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : (left < right)) (PreH7 : (right < heightSize_pre)) (PreH8 : (width = (right - left))) (PreH9 : (1 <= width)) (PreH10 : (width <= 99999)) (PreH11 : (shorterHeight = (LinearContainerHeight (l) (left) (right)))) (PreH12 : ((0 : Int) <= shorterHeight)) (PreH13 : (shorterHeight <= 10000)) (PreH14 : (area = (LinearContainerArea (l) (left) (right)))) (PreH15 : ((0 : Int) <= area)) (PreH16 : (area <= maximumArea)) (PreH17 : ((0 : Int) <= maximumArea)) (PreH18 : (maximumArea <= 999990000)) (PreH19 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (LinearContainerTwoPointerInvariant l left (right - 1) maximumArea)

noncomputable def maxAreaLinear_return_wit_1 : Prop :=
  (
forall (heightSize_pre : Int) (height_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : (left >= right)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : (left <= right)) (PreH7 : (right < heightSize_pre)) (PreH8 : ((0 : Int) <= maximumArea)) (PreH9 : (maximumArea <= 999990000)) (PreH10 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
|--
  “ (MaximumContainerArea l maximumArea) ”
  &&  (intArray.full height_pre heightSize_pre l)
) \/
(
forall (heightSize_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : (left >= right)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : (left <= right)) (PreH7 : (right < heightSize_pre)) (PreH8 : ((0 : Int) <= maximumArea)) (PreH9 : (maximumArea <= 999990000)) (PreH10 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ (MaximumContainerArea l maximumArea) ”
  &&  emp
)

noncomputable def maxAreaLinear_return_wit_1_split_goal_1 : Prop :=
  forall (heightSize_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : (left >= right)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : (left <= right)) (PreH7 : (right < heightSize_pre)) (PreH8 : ((0 : Int) <= maximumArea)) (PreH9 : (maximumArea <= 999990000)) (PreH10 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (MaximumContainerArea l maximumArea)

noncomputable def maxAreaLinear_partial_solve_wit_1 : Prop :=
  forall (heightSize_pre : Int) (height_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : (left < right)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : (left <= right)) (PreH7 : (right < heightSize_pre)) (PreH8 : ((0 : Int) <= maximumArea)) (PreH9 : (maximumArea <= 999990000)) (PreH10 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
|--
  “ (left < right) ” &&
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left <= right) ” &&
  “ (right < heightSize_pre) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (LinearContainerTwoPointerInvariant l left right maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (((height_pre + (left * sizeof(INT)))) # Int |-> ((Znth left l (0 : Int))))
  ** (intArray.missing_i height_pre left (0 : Int) heightSize_pre l)

noncomputable def maxAreaLinear_partial_solve_wit_2 : Prop :=
  forall (heightSize_pre : Int) (height_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : (left < right)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : (left <= right)) (PreH7 : (right < heightSize_pre)) (PreH8 : ((0 : Int) <= maximumArea)) (PreH9 : (maximumArea <= 999990000)) (PreH10 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
|--
  “ (left < right) ” &&
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left <= right) ” &&
  “ (right < heightSize_pre) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (LinearContainerTwoPointerInvariant l left right maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (((height_pre + (right * sizeof(INT)))) # Int |-> ((Znth right l (0 : Int))))
  ** (intArray.missing_i height_pre right (0 : Int) heightSize_pre l)

noncomputable def maxAreaLinear_partial_solve_wit_3 : Prop :=
  forall (heightSize_pre : Int) (height_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : ((Znth left l (0 : Int)) < (Znth right l (0 : Int)))) (PreH2 : (left < right)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : (left <= right)) (PreH8 : (right < heightSize_pre)) (PreH9 : ((0 : Int) <= maximumArea)) (PreH10 : (maximumArea <= 999990000)) (PreH11 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH13 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
|--
  “ ((Znth left l (0 : Int)) < (Znth right l (0 : Int))) ” &&
  “ (left < right) ” &&
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left <= right) ” &&
  “ (right < heightSize_pre) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (LinearContainerTwoPointerInvariant l left right maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (((height_pre + (left * sizeof(INT)))) # Int |-> ((Znth left l (0 : Int))))
  ** (intArray.missing_i height_pre left (0 : Int) heightSize_pre l)

noncomputable def maxAreaLinear_partial_solve_wit_4 : Prop :=
  forall (heightSize_pre : Int) (height_pre : Int) (l : (List Int)) (maximumArea : Int) (right : Int) (left : Int) (PreH1 : ((Znth left l (0 : Int)) >= (Znth right l (0 : Int)))) (PreH2 : (left < right)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : (left <= right)) (PreH8 : (right < heightSize_pre)) (PreH9 : ((0 : Int) <= maximumArea)) (PreH10 : (maximumArea <= 999990000)) (PreH11 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH13 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
|--
  “ ((Znth left l (0 : Int)) >= (Znth right l (0 : Int))) ” &&
  “ (left < right) ” &&
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left <= right) ” &&
  “ (right < heightSize_pre) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (LinearContainerTwoPointerInvariant l left right maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (((height_pre + (right * sizeof(INT)))) # Int |-> ((Znth right l (0 : Int))))
  ** (intArray.missing_i height_pre right (0 : Int) heightSize_pre l)

noncomputable def maxAreaLinear_partial_solve_wit_5 : Prop :=
  forall (heightSize_pre : Int) (height_pre : Int) (l : (List Int)) (left : Int) (right : Int) (width : Int) (shorterHeight : Int) (area : Int) (maximumArea : Int) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : ((0 : Int) <= left)) (PreH5 : (left < right)) (PreH6 : (right < heightSize_pre)) (PreH7 : (width = (right - left))) (PreH8 : (1 <= width)) (PreH9 : (width <= 99999)) (PreH10 : (shorterHeight = (LinearContainerHeight (l) (left) (right)))) (PreH11 : ((0 : Int) <= shorterHeight)) (PreH12 : (shorterHeight <= 10000)) (PreH13 : (area = (LinearContainerArea (l) (left) (right)))) (PreH14 : ((0 : Int) <= area)) (PreH15 : (area <= maximumArea)) (PreH16 : ((0 : Int) <= maximumArea)) (PreH17 : (maximumArea <= 999990000)) (PreH18 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH19 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH20 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
|--
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < right) ” &&
  “ (right < heightSize_pre) ” &&
  “ (width = (right - left)) ” &&
  “ (1 <= width) ” &&
  “ (width <= 99999) ” &&
  “ (shorterHeight = (LinearContainerHeight (l) (left) (right))) ” &&
  “ ((0 : Int) <= shorterHeight) ” &&
  “ (shorterHeight <= 10000) ” &&
  “ (area = (LinearContainerArea (l) (left) (right))) ” &&
  “ ((0 : Int) <= area) ” &&
  “ (area <= maximumArea) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (LinearContainerTwoPointerInvariant l left right maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (((height_pre + (left * sizeof(INT)))) # Int |-> ((Znth left l (0 : Int))))
  ** (intArray.missing_i height_pre left (0 : Int) heightSize_pre l)

noncomputable def maxAreaLinear_partial_solve_wit_6 : Prop :=
  forall (heightSize_pre : Int) (height_pre : Int) (l : (List Int)) (left : Int) (right : Int) (width : Int) (shorterHeight : Int) (area : Int) (maximumArea : Int) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : ((0 : Int) <= left)) (PreH5 : (left < right)) (PreH6 : (right < heightSize_pre)) (PreH7 : (width = (right - left))) (PreH8 : (1 <= width)) (PreH9 : (width <= 99999)) (PreH10 : (shorterHeight = (LinearContainerHeight (l) (left) (right)))) (PreH11 : ((0 : Int) <= shorterHeight)) (PreH12 : (shorterHeight <= 10000)) (PreH13 : (area = (LinearContainerArea (l) (left) (right)))) (PreH14 : ((0 : Int) <= area)) (PreH15 : (area <= maximumArea)) (PreH16 : ((0 : Int) <= maximumArea)) (PreH17 : (maximumArea <= 999990000)) (PreH18 : (LinearContainerTwoPointerInvariant l left right maximumArea)) (PreH19 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH20 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full height_pre heightSize_pre l)
|--
  “ (2 <= heightSize_pre) ” &&
  “ (heightSize_pre <= 100000) ” &&
  “ ((Zlength (l)) = heightSize_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < right) ” &&
  “ (right < heightSize_pre) ” &&
  “ (width = (right - left)) ” &&
  “ (1 <= width) ” &&
  “ (width <= 99999) ” &&
  “ (shorterHeight = (LinearContainerHeight (l) (left) (right))) ” &&
  “ ((0 : Int) <= shorterHeight) ” &&
  “ (shorterHeight <= 10000) ” &&
  “ (area = (LinearContainerArea (l) (left) (right))) ” &&
  “ ((0 : Int) <= area) ” &&
  “ (area <= maximumArea) ” &&
  “ ((0 : Int) <= maximumArea) ” &&
  “ (maximumArea <= 999990000) ” &&
  “ (LinearContainerTwoPointerInvariant l left right maximumArea) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (((height_pre + (right * sizeof(INT)))) # Int |-> ((Znth right l (0 : Int))))
  ** (intArray.missing_i height_pre right (0 : Int) heightSize_pre l)


structure VC_Correct : Type where
  proof_of_maxAreaLinear_safety_wit_1 : maxAreaLinear_safety_wit_1
  proof_of_maxAreaLinear_safety_wit_2 : maxAreaLinear_safety_wit_2
  proof_of_maxAreaLinear_safety_wit_3 : maxAreaLinear_safety_wit_3
  proof_of_maxAreaLinear_safety_wit_4 : maxAreaLinear_safety_wit_4
  proof_of_maxAreaLinear_safety_wit_5 : maxAreaLinear_safety_wit_5
  proof_of_maxAreaLinear_safety_wit_6 : maxAreaLinear_safety_wit_6
  proof_of_maxAreaLinear_safety_wit_7 : maxAreaLinear_safety_wit_7
  proof_of_maxAreaLinear_safety_wit_8 : maxAreaLinear_safety_wit_8
  proof_of_maxAreaLinear_safety_wit_9 : maxAreaLinear_safety_wit_9
  proof_of_maxAreaLinear_safety_wit_12 : maxAreaLinear_safety_wit_12
  proof_of_maxAreaLinear_safety_wit_13 : maxAreaLinear_safety_wit_13
  proof_of_maxAreaLinear_partial_solve_wit_1 : maxAreaLinear_partial_solve_wit_1
  proof_of_maxAreaLinear_partial_solve_wit_2 : maxAreaLinear_partial_solve_wit_2
  proof_of_maxAreaLinear_partial_solve_wit_3 : maxAreaLinear_partial_solve_wit_3
  proof_of_maxAreaLinear_partial_solve_wit_4 : maxAreaLinear_partial_solve_wit_4
  proof_of_maxAreaLinear_partial_solve_wit_5 : maxAreaLinear_partial_solve_wit_5
  proof_of_maxAreaLinear_partial_solve_wit_6 : maxAreaLinear_partial_solve_wit_6
  proof_of_maxAreaLinear_safety_wit_10 : maxAreaLinear_safety_wit_10
  proof_of_maxAreaLinear_safety_wit_11 : maxAreaLinear_safety_wit_11
  proof_of_maxAreaLinear_entail_wit_1 : maxAreaLinear_entail_wit_1
  proof_of_maxAreaLinear_entail_wit_2_1 : maxAreaLinear_entail_wit_2_1
  proof_of_maxAreaLinear_entail_wit_2_2 : maxAreaLinear_entail_wit_2_2
  proof_of_maxAreaLinear_entail_wit_2_3 : maxAreaLinear_entail_wit_2_3
  proof_of_maxAreaLinear_entail_wit_2_4 : maxAreaLinear_entail_wit_2_4
  proof_of_maxAreaLinear_entail_wit_3_1 : maxAreaLinear_entail_wit_3_1
  proof_of_maxAreaLinear_entail_wit_3_2 : maxAreaLinear_entail_wit_3_2
  proof_of_maxAreaLinear_return_wit_1 : maxAreaLinear_return_wit_1

end SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_linear.container_with_most_water_linear_goal
