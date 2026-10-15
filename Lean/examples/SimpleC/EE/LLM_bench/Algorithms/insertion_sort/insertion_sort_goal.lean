import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.insertion_sort.insertion_sort_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.insertion_sort.insertion_sort_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance insertion_sort_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def sortArray_safety_wit_1 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (PreH1 : ((Zlength (l)) = numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "returnSize" ) )) # Ptr |-> (returnSize_pre))
  ** (intArray.full nums_pre numsSize_pre l)
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def sortArray_safety_wit_2 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (i : Int) (l0 : (List Int)) (l3 : (List Int)) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l = (l1 ++ l2))) (PreH5 : (l3 = (l0 ++ l2))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l1)))) (PreH8 : (1 <= i)) (PreH9 : (i <= numsSize_pre)) (PreH10 : (Permutation l1 l0)) (PreH11 : (increasing l0)) ,
  ((( &( "j" ) )) # Int |->_)
  ** (intArray.full nums_pre numsSize_pre l3)
  ** ((( &( "key" ) )) # Int |-> ((Znth i l3 (0 : Int))))
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "returnSize" ) )) # Ptr |-> (returnSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def sortArray_safety_wit_3 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (i : Int) (l0 : (List Int)) (l3 : (List Int)) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l = (l1 ++ l2))) (PreH5 : (l3 = (l0 ++ l2))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l1)))) (PreH8 : (1 <= i)) (PreH9 : (i <= numsSize_pre)) (PreH10 : (Permutation l1 l0)) (PreH11 : (increasing l0)) ,
  ((( &( "j" ) )) # Int |->_)
  ** (intArray.full nums_pre numsSize_pre l3)
  ** ((( &( "key" ) )) # Int |-> ((Znth i l3 (0 : Int))))
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "returnSize" ) )) # Ptr |-> (returnSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def sortArray_safety_wit_4 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (l5 : (List Int)) (l2 : (List Int)) (l3 : (List Int)) (l0 : (List Int)) (i : Int) (l1 : (List Int)) (key : Int) (l4 : (List Int)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 50000)) (PreH3 : (l = (l1 ++ (key :: l4)))) (PreH4 : (numsSize_pre = (Zlength (l)))) (PreH5 : (i = (Zlength (l1)))) (PreH6 : (1 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : (Permutation l1 l0)) (PreH9 : (increasing l0)) (PreH10 : (l0 = (l2 ++ l3))) (PreH11 : (l5 = ((l2 ++ ((Znth ((j + 1)) (l0) (key)) :: l3)) ++ l4))) (PreH12 : ((0 : Int) <= (j + 1))) (PreH13 : ((j + 1) = (Zlength (l2)))) (PreH14 : ((j + 1) <= i)) (PreH15 : ((j + 1) < numsSize_pre)) (PreH16 : (strict_lowerbound key l3)) ,
  ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "returnSize" ) )) # Ptr |-> (returnSize_pre))
  ** ((( &( "key" ) )) # Int |-> (key))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
  ** (intArray.full nums_pre numsSize_pre l5)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def sortArray_safety_wit_5 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (l5 : (List Int)) (l2 : (List Int)) (l3 : (List Int)) (l0 : (List Int)) (i : Int) (l1 : (List Int)) (key : Int) (l4 : (List Int)) (PreH1 : ((Znth j l5 (0 : Int)) > key)) (PreH2 : (j >= (0 : Int))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l = (l1 ++ (key :: l4)))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l1)))) (PreH8 : (1 <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (Permutation l1 l0)) (PreH11 : (increasing l0)) (PreH12 : (l0 = (l2 ++ l3))) (PreH13 : (l5 = ((l2 ++ ((Znth ((j + 1)) (l0) (key)) :: l3)) ++ l4))) (PreH14 : ((0 : Int) <= (j + 1))) (PreH15 : ((j + 1) = (Zlength (l2)))) (PreH16 : ((j + 1) <= i)) (PreH17 : ((j + 1) < numsSize_pre)) (PreH18 : (strict_lowerbound key l3)) ,
  (intArray.full nums_pre numsSize_pre l5)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "returnSize" ) )) # Ptr |-> (returnSize_pre))
  ** ((( &( "key" ) )) # Int |-> (key))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def sortArray_safety_wit_6 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (l5 : (List Int)) (l2 : (List Int)) (l3 : (List Int)) (l0 : (List Int)) (i : Int) (l1 : (List Int)) (key : Int) (l4 : (List Int)) (PreH1 : ((Znth j l5 (0 : Int)) > key)) (PreH2 : (j >= (0 : Int))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l = (l1 ++ (key :: l4)))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l1)))) (PreH8 : (1 <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (Permutation l1 l0)) (PreH11 : (increasing l0)) (PreH12 : (l0 = (l2 ++ l3))) (PreH13 : (l5 = ((l2 ++ ((Znth ((j + 1)) (l0) (key)) :: l3)) ++ l4))) (PreH14 : ((0 : Int) <= (j + 1))) (PreH15 : ((j + 1) = (Zlength (l2)))) (PreH16 : ((j + 1) <= i)) (PreH17 : ((j + 1) < numsSize_pre)) (PreH18 : (strict_lowerbound key l3)) ,
  (intArray.full nums_pre numsSize_pre l5)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "returnSize" ) )) # Ptr |-> (returnSize_pre))
  ** ((( &( "key" ) )) # Int |-> (key))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def sortArray_safety_wit_7 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (l5 : (List Int)) (l2 : (List Int)) (l3 : (List Int)) (l0 : (List Int)) (i : Int) (l1 : (List Int)) (key : Int) (l4 : (List Int)) (PreH1 : ((Znth j l5 (0 : Int)) > key)) (PreH2 : (j >= (0 : Int))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l = (l1 ++ (key :: l4)))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l1)))) (PreH8 : (1 <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (Permutation l1 l0)) (PreH11 : (increasing l0)) (PreH12 : (l0 = (l2 ++ l3))) (PreH13 : (l5 = ((l2 ++ ((Znth ((j + 1)) (l0) (key)) :: l3)) ++ l4))) (PreH14 : ((0 : Int) <= (j + 1))) (PreH15 : ((j + 1) = (Zlength (l2)))) (PreH16 : ((j + 1) <= i)) (PreH17 : ((j + 1) < numsSize_pre)) (PreH18 : (strict_lowerbound key l3)) ,
  (intArray.full nums_pre numsSize_pre (replace_Znth ((j + 1)) ((Znth j l5 (0 : Int))) (l5)))
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "returnSize" ) )) # Ptr |-> (returnSize_pre))
  ** ((( &( "key" ) )) # Int |-> (key))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
|--
  “ ((j - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j - 1)) ”

noncomputable def sortArray_safety_wit_8 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (l5 : (List Int)) (l2 : (List Int)) (l3 : (List Int)) (l0 : (List Int)) (i : Int) (l1 : (List Int)) (key : Int) (l4 : (List Int)) (PreH1 : ((Znth j l5 (0 : Int)) <= key)) (PreH2 : (j >= (0 : Int))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l = (l1 ++ (key :: l4)))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l1)))) (PreH8 : (1 <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (Permutation l1 l0)) (PreH11 : (increasing l0)) (PreH12 : (l0 = (l2 ++ l3))) (PreH13 : (l5 = ((l2 ++ ((Znth ((j + 1)) (l0) (key)) :: l3)) ++ l4))) (PreH14 : ((0 : Int) <= (j + 1))) (PreH15 : ((j + 1) = (Zlength (l2)))) (PreH16 : ((j + 1) <= i)) (PreH17 : ((j + 1) < numsSize_pre)) (PreH18 : (strict_lowerbound key l3)) ,
  (intArray.full nums_pre numsSize_pre l5)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "returnSize" ) )) # Ptr |-> (returnSize_pre))
  ** ((( &( "key" ) )) # Int |-> (key))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def sortArray_safety_wit_9 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (l5 : (List Int)) (l2 : (List Int)) (l3 : (List Int)) (l0 : (List Int)) (i : Int) (l1 : (List Int)) (key : Int) (l4 : (List Int)) (PreH1 : (j < (0 : Int))) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l = (l1 ++ (key :: l4)))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l1)))) (PreH7 : (1 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (Permutation l1 l0)) (PreH10 : (increasing l0)) (PreH11 : (l0 = (l2 ++ l3))) (PreH12 : (l5 = ((l2 ++ ((Znth ((j + 1)) (l0) (key)) :: l3)) ++ l4))) (PreH13 : ((0 : Int) <= (j + 1))) (PreH14 : ((j + 1) = (Zlength (l2)))) (PreH15 : ((j + 1) <= i)) (PreH16 : ((j + 1) < numsSize_pre)) (PreH17 : (strict_lowerbound key l3)) ,
  ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "returnSize" ) )) # Ptr |-> (returnSize_pre))
  ** ((( &( "key" ) )) # Int |-> (key))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
  ** (intArray.full nums_pre numsSize_pre l5)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def sortArray_safety_wit_10 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (l5 : (List Int)) (l2 : (List Int)) (l3 : (List Int)) (l0 : (List Int)) (i : Int) (l1 : (List Int)) (key : Int) (l4 : (List Int)) (PreH1 : (j < (0 : Int))) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l = (l1 ++ (key :: l4)))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l1)))) (PreH7 : (1 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (Permutation l1 l0)) (PreH10 : (increasing l0)) (PreH11 : (l0 = (l2 ++ l3))) (PreH12 : (l5 = ((l2 ++ ((Znth ((j + 1)) (l0) (key)) :: l3)) ++ l4))) (PreH13 : ((0 : Int) <= (j + 1))) (PreH14 : ((j + 1) = (Zlength (l2)))) (PreH15 : ((j + 1) <= i)) (PreH16 : ((j + 1) < numsSize_pre)) (PreH17 : (strict_lowerbound key l3)) ,
  ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "returnSize" ) )) # Ptr |-> (returnSize_pre))
  ** ((( &( "key" ) )) # Int |-> (key))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
  ** (intArray.full nums_pre numsSize_pre l5)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def sortArray_safety_wit_11 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (l5 : (List Int)) (l2 : (List Int)) (l3 : (List Int)) (l0 : (List Int)) (i : Int) (l1 : (List Int)) (key : Int) (l4 : (List Int)) (PreH1 : ((Znth j l5 (0 : Int)) <= key)) (PreH2 : (j >= (0 : Int))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l = (l1 ++ (key :: l4)))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l1)))) (PreH8 : (1 <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (Permutation l1 l0)) (PreH11 : (increasing l0)) (PreH12 : (l0 = (l2 ++ l3))) (PreH13 : (l5 = ((l2 ++ ((Znth ((j + 1)) (l0) (key)) :: l3)) ++ l4))) (PreH14 : ((0 : Int) <= (j + 1))) (PreH15 : ((j + 1) = (Zlength (l2)))) (PreH16 : ((j + 1) <= i)) (PreH17 : ((j + 1) < numsSize_pre)) (PreH18 : (strict_lowerbound key l3)) ,
  (intArray.full nums_pre numsSize_pre l5)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "returnSize" ) )) # Ptr |-> (returnSize_pre))
  ** ((( &( "key" ) )) # Int |-> (key))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def sortArray_safety_wit_12 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (l5 : (List Int)) (l2 : (List Int)) (l3 : (List Int)) (l0 : (List Int)) (i : Int) (l1 : (List Int)) (key : Int) (l4 : (List Int)) (PreH1 : (j < (0 : Int))) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l = (l1 ++ (key :: l4)))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l1)))) (PreH7 : (1 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (Permutation l1 l0)) (PreH10 : (increasing l0)) (PreH11 : (l0 = (l2 ++ l3))) (PreH12 : (l5 = ((l2 ++ ((Znth ((j + 1)) (l0) (key)) :: l3)) ++ l4))) (PreH13 : ((0 : Int) <= (j + 1))) (PreH14 : ((j + 1) = (Zlength (l2)))) (PreH15 : ((j + 1) <= i)) (PreH16 : ((j + 1) < numsSize_pre)) (PreH17 : (strict_lowerbound key l3)) ,
  (intArray.full nums_pre numsSize_pre (replace_Znth ((j + 1)) (key) (l5)))
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "returnSize" ) )) # Ptr |-> (returnSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def sortArray_safety_wit_13 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (l5 : (List Int)) (l2 : (List Int)) (l3 : (List Int)) (l0 : (List Int)) (i : Int) (l1 : (List Int)) (key : Int) (l4 : (List Int)) (PreH1 : ((Znth j l5 (0 : Int)) <= key)) (PreH2 : (j >= (0 : Int))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l = (l1 ++ (key :: l4)))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l1)))) (PreH8 : (1 <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (Permutation l1 l0)) (PreH11 : (increasing l0)) (PreH12 : (l0 = (l2 ++ l3))) (PreH13 : (l5 = ((l2 ++ ((Znth ((j + 1)) (l0) (key)) :: l3)) ++ l4))) (PreH14 : ((0 : Int) <= (j + 1))) (PreH15 : ((j + 1) = (Zlength (l2)))) (PreH16 : ((j + 1) <= i)) (PreH17 : ((j + 1) < numsSize_pre)) (PreH18 : (strict_lowerbound key l3)) ,
  (intArray.full nums_pre numsSize_pre (replace_Znth ((j + 1)) (key) (l5)))
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "returnSize" ) )) # Ptr |-> (returnSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def sortArray_entail_wit_1 : Prop :=
  (
forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (PreH1 : ((Zlength (l)) = numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) ,
  (intArray.full nums_pre numsSize_pre l)
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
|--
  EX l0 : (List Int), EX l3 : (List Int), EX l1 : (List Int), EX l2 : (List Int),
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ (l = (l1 ++ l2)) ” &&
  “ (l3 = (l0 ++ l2)) ” &&
  “ (numsSize_pre = (Zlength (l))) ” &&
  “ (1 = (Zlength (l1))) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= numsSize_pre) ” &&
  “ (Permutation l1 l0) ” &&
  “ (increasing l0) ”
  &&  ((returnSize_pre) # Int |-> (numsSize_pre))
  ** (intArray.full nums_pre numsSize_pre l3)
) \/
(
forall (numsSize_pre : Int) (l : (List Int)) (PreH1 : ((Zlength (l)) = numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) ,
  TT && emp 
|--
  EX l0 : (List Int), EX l1 : (List Int), EX l2 : (List Int),
  “ (l = (l0 ++ l2)) ” &&
  “ (l = (l1 ++ l2)) ” &&
  “ ((Zlength (l)) = (Zlength (l))) ” &&
  “ (1 = (Zlength (l1))) ” &&
  “ (1 <= 1) ” &&
  “ (Permutation l1 l0) ” &&
  “ (increasing l0) ”
  &&  emp
)

noncomputable def sortArray_entail_wit_2 : Prop :=
  (
forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (i : Int) (l0_2 : (List Int)) (l3 : (List Int)) (l1_2 : (List Int)) (l2_2 : (List Int)) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l = (l1_2 ++ l2_2))) (PreH5 : (l3 = (l0_2 ++ l2_2))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l1_2)))) (PreH8 : (1 <= i)) (PreH9 : (i <= numsSize_pre)) (PreH10 : (Permutation l1_2 l0_2)) (PreH11 : (increasing l0_2)) ,
  (intArray.full nums_pre numsSize_pre l3)
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
|--
  EX l5 : (List Int), EX l2 : (List Int), EX l3_2 : (List Int), EX l0 : (List Int), EX l1 : (List Int), EX l4 : (List Int),
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ (l = (l1 ++ ((Znth i l3 (0 : Int)) :: l4))) ” &&
  “ (numsSize_pre = (Zlength (l))) ” &&
  “ (i = (Zlength (l1))) ” &&
  “ (1 <= i) ” &&
  “ (i < numsSize_pre) ” &&
  “ (Permutation l1 l0) ” &&
  “ (increasing l0) ” &&
  “ (l0 = (l2 ++ l3_2)) ” &&
  “ (l5 = ((l2 ++ ((Znth (((i - 1) + 1)) (l0) ((Znth i l3 (0 : Int)))) :: l3_2)) ++ l4)) ” &&
  “ ((0 : Int) <= ((i - 1) + 1)) ” &&
  “ (((i - 1) + 1) = (Zlength (l2))) ” &&
  “ (((i - 1) + 1) <= i) ” &&
  “ (((i - 1) + 1) < numsSize_pre) ” &&
  “ (strict_lowerbound (Znth i l3 (0 : Int)) l3_2) ”
  &&  ((returnSize_pre) # Int |-> (numsSize_pre))
  ** (intArray.full nums_pre numsSize_pre l5)
) \/
(
forall (numsSize_pre : Int) (l : (List Int)) (i : Int) (l0_2 : (List Int)) (l3 : (List Int)) (l1_2 : (List Int)) (l2_2 : (List Int)) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l = (l1_2 ++ l2_2))) (PreH5 : (l3 = (l0_2 ++ l2_2))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l1_2)))) (PreH8 : (1 <= i)) (PreH9 : (i <= numsSize_pre)) (PreH10 : (Permutation l1_2 l0_2)) (PreH11 : (increasing l0_2)) ,
  TT && emp 
|--
  EX l2 : (List Int), EX l3_2 : (List Int), EX l1 : (List Int), EX l4 : (List Int),
  “ ((l0_2 ++ l2_2) = ((l2 ++ ((Znth ((((Zlength (l1_2)) - 1) + 1)) ((l2 ++ l3_2)) ((Znth (Zlength (l1_2)) (l0_2 ++ l2_2) (0 : Int)))) :: l3_2)) ++ l4)) ” &&
  “ ((l1_2 ++ l2_2) = (l1 ++ ((Znth (Zlength (l1_2)) (l0_2 ++ l2_2) (0 : Int)) :: l4))) ” &&
  “ ((Zlength (l1_2)) = (Zlength (l1))) ” &&
  “ (Permutation l1 (l2 ++ l3_2)) ” &&
  “ (increasing (l2 ++ l3_2)) ” &&
  “ ((0 : Int) <= (((Zlength (l1_2)) - 1) + 1)) ” &&
  “ ((((Zlength (l1_2)) - 1) + 1) = (Zlength (l2))) ” &&
  “ ((((Zlength (l1_2)) - 1) + 1) <= (Zlength (l1_2))) ” &&
  “ ((((Zlength (l1_2)) - 1) + 1) < (Zlength (l))) ” &&
  “ (strict_lowerbound (Znth (Zlength (l1_2)) (l0_2 ++ l2_2) (0 : Int)) l3_2) ”
  &&  emp
)

noncomputable def sortArray_entail_wit_3 : Prop :=
  (
forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (l5_2 : (List Int)) (l2_2 : (List Int)) (l3_2 : (List Int)) (l0_2 : (List Int)) (i : Int) (l1_2 : (List Int)) (key : Int) (l4_2 : (List Int)) (PreH1 : ((Znth j l5_2 (0 : Int)) > key)) (PreH2 : (j >= (0 : Int))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l = (l1_2 ++ (key :: l4_2)))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l1_2)))) (PreH8 : (1 <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (Permutation l1_2 l0_2)) (PreH11 : (increasing l0_2)) (PreH12 : (l0_2 = (l2_2 ++ l3_2))) (PreH13 : (l5_2 = ((l2_2 ++ ((Znth ((j + 1)) (l0_2) (key)) :: l3_2)) ++ l4_2))) (PreH14 : ((0 : Int) <= (j + 1))) (PreH15 : ((j + 1) = (Zlength (l2_2)))) (PreH16 : ((j + 1) <= i)) (PreH17 : ((j + 1) < numsSize_pre)) (PreH18 : (strict_lowerbound key l3_2)) ,
  (intArray.full nums_pre numsSize_pre (replace_Znth ((j + 1)) ((Znth j l5_2 (0 : Int))) (l5_2)))
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
|--
  EX l5 : (List Int), EX l2 : (List Int), EX l3 : (List Int), EX l0 : (List Int), EX l1 : (List Int), EX l4 : (List Int),
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ (l = (l1 ++ (key :: l4))) ” &&
  “ (numsSize_pre = (Zlength (l))) ” &&
  “ (i = (Zlength (l1))) ” &&
  “ (1 <= i) ” &&
  “ (i < numsSize_pre) ” &&
  “ (Permutation l1 l0) ” &&
  “ (increasing l0) ” &&
  “ (l0 = (l2 ++ l3)) ” &&
  “ (l5 = ((l2 ++ ((Znth (((j - 1) + 1)) (l0) (key)) :: l3)) ++ l4)) ” &&
  “ ((0 : Int) <= ((j - 1) + 1)) ” &&
  “ (((j - 1) + 1) = (Zlength (l2))) ” &&
  “ (((j - 1) + 1) <= i) ” &&
  “ (((j - 1) + 1) < numsSize_pre) ” &&
  “ (strict_lowerbound key l3) ”
  &&  ((returnSize_pre) # Int |-> (numsSize_pre))
  ** (intArray.full nums_pre numsSize_pre l5)
) \/
(
forall (numsSize_pre : Int) (l : (List Int)) (j : Int) (l5_2 : (List Int)) (l2_2 : (List Int)) (l3_2 : (List Int)) (l0_2 : (List Int)) (i : Int) (l1_2 : (List Int)) (key : Int) (l4_2 : (List Int)) (PreH1 : ((Znth j l5_2 (0 : Int)) > key)) (PreH2 : (j >= (0 : Int))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l = (l1_2 ++ (key :: l4_2)))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l1_2)))) (PreH8 : (1 <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (Permutation l1_2 l0_2)) (PreH11 : (increasing l0_2)) (PreH12 : (l0_2 = (l2_2 ++ l3_2))) (PreH13 : (l5_2 = ((l2_2 ++ ((Znth ((j + 1)) (l0_2) (key)) :: l3_2)) ++ l4_2))) (PreH14 : ((0 : Int) <= (j + 1))) (PreH15 : ((j + 1) = (Zlength (l2_2)))) (PreH16 : ((j + 1) <= i)) (PreH17 : ((j + 1) < numsSize_pre)) (PreH18 : (strict_lowerbound key l3_2)) ,
  TT && emp 
|--
  EX l2 : (List Int), EX l3 : (List Int), EX l1 : (List Int), EX l4 : (List Int),
  “ ((replace_Znth ((j + 1)) ((Znth j ((l2_2 ++ ((Znth ((j + 1)) (l0_2) (key)) :: l3_2)) ++ l4_2) (0 : Int))) (((l2_2 ++ ((Znth ((j + 1)) (l0_2) (key)) :: l3_2)) ++ l4_2))) = ((l2 ++ ((Znth (((j - 1) + 1)) ((l2 ++ l3)) (key)) :: l3)) ++ l4)) ” &&
  “ ((l1_2 ++ (key :: l4_2)) = (l1 ++ (key :: l4))) ” &&
  “ ((Zlength (l1_2)) = (Zlength (l1))) ” &&
  “ (Permutation l1 (l2 ++ l3)) ” &&
  “ (increasing (l2 ++ l3)) ” &&
  “ ((0 : Int) <= ((j - 1) + 1)) ” &&
  “ (((j - 1) + 1) = (Zlength (l2))) ” &&
  “ (((j - 1) + 1) <= (Zlength (l1_2))) ” &&
  “ (((j - 1) + 1) < (Zlength (l))) ” &&
  “ (strict_lowerbound key l3) ”
  &&  emp
)

noncomputable def sortArray_entail_wit_4_1 : Prop :=
  (
forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (l5 : (List Int)) (l2_2 : (List Int)) (l3_2 : (List Int)) (l0_2 : (List Int)) (i : Int) (l1_2 : (List Int)) (key : Int) (l4 : (List Int)) (PreH1 : (j < (0 : Int))) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l = (l1_2 ++ (key :: l4)))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l1_2)))) (PreH7 : (1 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (Permutation l1_2 l0_2)) (PreH10 : (increasing l0_2)) (PreH11 : (l0_2 = (l2_2 ++ l3_2))) (PreH12 : (l5 = ((l2_2 ++ ((Znth ((j + 1)) (l0_2) (key)) :: l3_2)) ++ l4))) (PreH13 : ((0 : Int) <= (j + 1))) (PreH14 : ((j + 1) = (Zlength (l2_2)))) (PreH15 : ((j + 1) <= i)) (PreH16 : ((j + 1) < numsSize_pre)) (PreH17 : (strict_lowerbound key l3_2)) ,
  (intArray.full nums_pre numsSize_pre (replace_Znth ((j + 1)) (key) (l5)))
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
|--
  EX l0 : (List Int), EX l3 : (List Int), EX l1 : (List Int), EX l2 : (List Int),
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ (l = (l1 ++ l2)) ” &&
  “ (l3 = (l0 ++ l2)) ” &&
  “ (numsSize_pre = (Zlength (l))) ” &&
  “ ((i + 1) = (Zlength (l1))) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= numsSize_pre) ” &&
  “ (Permutation l1 l0) ” &&
  “ (increasing l0) ”
  &&  ((returnSize_pre) # Int |-> (numsSize_pre))
  ** (intArray.full nums_pre numsSize_pre l3)
) \/
(
forall (numsSize_pre : Int) (l : (List Int)) (j : Int) (l5 : (List Int)) (l2_2 : (List Int)) (l3_2 : (List Int)) (l0_2 : (List Int)) (i : Int) (l1_2 : (List Int)) (key : Int) (l4 : (List Int)) (PreH1 : (j < (0 : Int))) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l = (l1_2 ++ (key :: l4)))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l1_2)))) (PreH7 : (1 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (Permutation l1_2 l0_2)) (PreH10 : (increasing l0_2)) (PreH11 : (l0_2 = (l2_2 ++ l3_2))) (PreH12 : (l5 = ((l2_2 ++ ((Znth ((j + 1)) (l0_2) (key)) :: l3_2)) ++ l4))) (PreH13 : ((0 : Int) <= (j + 1))) (PreH14 : ((j + 1) = (Zlength (l2_2)))) (PreH15 : ((j + 1) <= i)) (PreH16 : ((j + 1) < numsSize_pre)) (PreH17 : (strict_lowerbound key l3_2)) ,
  TT && emp 
|--
  EX l0 : (List Int), EX l1 : (List Int), EX l2 : (List Int),
  “ ((replace_Znth ((j + 1)) (key) (((l2_2 ++ ((Znth ((j + 1)) (l0_2) (key)) :: l3_2)) ++ l4))) = (l0 ++ l2)) ” &&
  “ ((l1_2 ++ (key :: l4)) = (l1 ++ l2)) ” &&
  “ (((Zlength (l1_2)) + 1) = (Zlength (l1))) ” &&
  “ (1 <= ((Zlength (l1_2)) + 1)) ” &&
  “ (((Zlength (l1_2)) + 1) <= (Zlength (l))) ” &&
  “ (Permutation l1 l0) ” &&
  “ (increasing l0) ”
  &&  emp
)

noncomputable def sortArray_entail_wit_4_2 : Prop :=
  (
forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (l5 : (List Int)) (l2_2 : (List Int)) (l3_2 : (List Int)) (l0_2 : (List Int)) (i : Int) (l1_2 : (List Int)) (key : Int) (l4 : (List Int)) (PreH1 : ((Znth j l5 (0 : Int)) <= key)) (PreH2 : (j >= (0 : Int))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l = (l1_2 ++ (key :: l4)))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l1_2)))) (PreH8 : (1 <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (Permutation l1_2 l0_2)) (PreH11 : (increasing l0_2)) (PreH12 : (l0_2 = (l2_2 ++ l3_2))) (PreH13 : (l5 = ((l2_2 ++ ((Znth ((j + 1)) (l0_2) (key)) :: l3_2)) ++ l4))) (PreH14 : ((0 : Int) <= (j + 1))) (PreH15 : ((j + 1) = (Zlength (l2_2)))) (PreH16 : ((j + 1) <= i)) (PreH17 : ((j + 1) < numsSize_pre)) (PreH18 : (strict_lowerbound key l3_2)) ,
  (intArray.full nums_pre numsSize_pre (replace_Znth ((j + 1)) (key) (l5)))
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
|--
  EX l0 : (List Int), EX l3 : (List Int), EX l1 : (List Int), EX l2 : (List Int),
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ (l = (l1 ++ l2)) ” &&
  “ (l3 = (l0 ++ l2)) ” &&
  “ (numsSize_pre = (Zlength (l))) ” &&
  “ ((i + 1) = (Zlength (l1))) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= numsSize_pre) ” &&
  “ (Permutation l1 l0) ” &&
  “ (increasing l0) ”
  &&  ((returnSize_pre) # Int |-> (numsSize_pre))
  ** (intArray.full nums_pre numsSize_pre l3)
) \/
(
forall (numsSize_pre : Int) (l : (List Int)) (j : Int) (l5 : (List Int)) (l2_2 : (List Int)) (l3_2 : (List Int)) (l0_2 : (List Int)) (i : Int) (l1_2 : (List Int)) (key : Int) (l4 : (List Int)) (PreH1 : ((Znth j l5 (0 : Int)) <= key)) (PreH2 : (j >= (0 : Int))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l = (l1_2 ++ (key :: l4)))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l1_2)))) (PreH8 : (1 <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (Permutation l1_2 l0_2)) (PreH11 : (increasing l0_2)) (PreH12 : (l0_2 = (l2_2 ++ l3_2))) (PreH13 : (l5 = ((l2_2 ++ ((Znth ((j + 1)) (l0_2) (key)) :: l3_2)) ++ l4))) (PreH14 : ((0 : Int) <= (j + 1))) (PreH15 : ((j + 1) = (Zlength (l2_2)))) (PreH16 : ((j + 1) <= i)) (PreH17 : ((j + 1) < numsSize_pre)) (PreH18 : (strict_lowerbound key l3_2)) ,
  TT && emp 
|--
  EX l0 : (List Int), EX l1 : (List Int), EX l2 : (List Int),
  “ ((replace_Znth ((j + 1)) (key) (((l2_2 ++ ((Znth ((j + 1)) (l0_2) (key)) :: l3_2)) ++ l4))) = (l0 ++ l2)) ” &&
  “ ((l1_2 ++ (key :: l4)) = (l1 ++ l2)) ” &&
  “ (((Zlength (l1_2)) + 1) = (Zlength (l1))) ” &&
  “ (1 <= ((Zlength (l1_2)) + 1)) ” &&
  “ (((Zlength (l1_2)) + 1) <= (Zlength (l))) ” &&
  “ (Permutation l1 l0) ” &&
  “ (increasing l0) ”
  &&  emp
)

noncomputable def sortArray_return_wit_1 : Prop :=
  (
forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (i : Int) (l0 : (List Int)) (l3 : (List Int)) (l1_2 : (List Int)) (l2 : (List Int)) (PreH1 : (i >= numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l = (l1_2 ++ l2))) (PreH5 : (l3 = (l0 ++ l2))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l1_2)))) (PreH8 : (1 <= i)) (PreH9 : (i <= numsSize_pre)) (PreH10 : (Permutation l1_2 l0)) (PreH11 : (increasing l0)) ,
  ((returnSize_pre) # Int |-> (numsSize_pre))
  ** (intArray.full nums_pre numsSize_pre l3)
|--
  EX l1 : (List Int),
  “ (Permutation l l1) ” &&
  “ (increasing l1) ”
  &&  (intArray.full nums_pre numsSize_pre l1)
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
) \/
(
forall (numsSize_pre : Int) (l : (List Int)) (i : Int) (l0 : (List Int)) (l3 : (List Int)) (l1_2 : (List Int)) (l2 : (List Int)) (PreH1 : (i >= numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l = (l1_2 ++ l2))) (PreH5 : (l3 = (l0 ++ l2))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l1_2)))) (PreH8 : (1 <= i)) (PreH9 : (i <= numsSize_pre)) (PreH10 : (Permutation l1_2 l0)) (PreH11 : (increasing l0)) ,
  TT && emp 
|--
  “ (increasing l3) ” &&
  “ (Permutation l l3) ”
  &&  emp
)

noncomputable def sortArray_return_wit_1_split_goal_1 : Prop :=
  forall (numsSize_pre : Int) (l : (List Int)) (i : Int) (l0 : (List Int)) (l3 : (List Int)) (l1_2 : (List Int)) (l2 : (List Int)) (PreH1 : (i >= numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l = (l1_2 ++ l2))) (PreH5 : (l3 = (l0 ++ l2))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l1_2)))) (PreH8 : (1 <= i)) (PreH9 : (i <= numsSize_pre)) (PreH10 : (Permutation l1_2 l0)) (PreH11 : (increasing l0)) ,
  (increasing l3)

noncomputable def sortArray_return_wit_1_split_goal_2 : Prop :=
  forall (numsSize_pre : Int) (l : (List Int)) (i : Int) (l0 : (List Int)) (l3 : (List Int)) (l1_2 : (List Int)) (l2 : (List Int)) (PreH1 : (i >= numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l = (l1_2 ++ l2))) (PreH5 : (l3 = (l0 ++ l2))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l1_2)))) (PreH8 : (1 <= i)) (PreH9 : (i <= numsSize_pre)) (PreH10 : (Permutation l1_2 l0)) (PreH11 : (increasing l0)) ,
  (Permutation l l3)

noncomputable def sortArray_partial_solve_wit_1 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (i : Int) (l0 : (List Int)) (l3 : (List Int)) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l = (l1 ++ l2))) (PreH5 : (l3 = (l0 ++ l2))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l1)))) (PreH8 : (1 <= i)) (PreH9 : (i <= numsSize_pre)) (PreH10 : (Permutation l1 l0)) (PreH11 : (increasing l0)) ,
  ((returnSize_pre) # Int |-> (numsSize_pre))
  ** (intArray.full nums_pre numsSize_pre l3)
|--
  “ (i < numsSize_pre) ” &&
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ (l = (l1 ++ l2)) ” &&
  “ (l3 = (l0 ++ l2)) ” &&
  “ (numsSize_pre = (Zlength (l))) ” &&
  “ (i = (Zlength (l1))) ” &&
  “ (1 <= i) ” &&
  “ (i <= numsSize_pre) ” &&
  “ (Permutation l1 l0) ” &&
  “ (increasing l0) ”
  &&  (((nums_pre + (i * sizeof(INT)))) # Int |-> ((Znth i l3 (0 : Int))))
  ** (intArray.missing_i nums_pre i (0 : Int) numsSize_pre l3)
  ** ((returnSize_pre) # Int |-> (numsSize_pre))

noncomputable def sortArray_partial_solve_wit_2 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (l5 : (List Int)) (l2 : (List Int)) (l3 : (List Int)) (l0 : (List Int)) (i : Int) (l1 : (List Int)) (key : Int) (l4 : (List Int)) (PreH1 : (j >= (0 : Int))) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l = (l1 ++ (key :: l4)))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l1)))) (PreH7 : (1 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (Permutation l1 l0)) (PreH10 : (increasing l0)) (PreH11 : (l0 = (l2 ++ l3))) (PreH12 : (l5 = ((l2 ++ ((Znth ((j + 1)) (l0) (key)) :: l3)) ++ l4))) (PreH13 : ((0 : Int) <= (j + 1))) (PreH14 : ((j + 1) = (Zlength (l2)))) (PreH15 : ((j + 1) <= i)) (PreH16 : ((j + 1) < numsSize_pre)) (PreH17 : (strict_lowerbound key l3)) ,
  ((returnSize_pre) # Int |-> (numsSize_pre))
  ** (intArray.full nums_pre numsSize_pre l5)
|--
  “ (j >= (0 : Int)) ” &&
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ (l = (l1 ++ (key :: l4))) ” &&
  “ (numsSize_pre = (Zlength (l))) ” &&
  “ (i = (Zlength (l1))) ” &&
  “ (1 <= i) ” &&
  “ (i < numsSize_pre) ” &&
  “ (Permutation l1 l0) ” &&
  “ (increasing l0) ” &&
  “ (l0 = (l2 ++ l3)) ” &&
  “ (l5 = ((l2 ++ ((Znth ((j + 1)) (l0) (key)) :: l3)) ++ l4)) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) = (Zlength (l2))) ” &&
  “ ((j + 1) <= i) ” &&
  “ ((j + 1) < numsSize_pre) ” &&
  “ (strict_lowerbound key l3) ”
  &&  (((nums_pre + (j * sizeof(INT)))) # Int |-> ((Znth j l5 (0 : Int))))
  ** (intArray.missing_i nums_pre j (0 : Int) numsSize_pre l5)
  ** ((returnSize_pre) # Int |-> (numsSize_pre))

noncomputable def sortArray_partial_solve_wit_3 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (l5 : (List Int)) (l2 : (List Int)) (l3 : (List Int)) (l0 : (List Int)) (i : Int) (l1 : (List Int)) (key : Int) (l4 : (List Int)) (PreH1 : ((Znth j l5 (0 : Int)) > key)) (PreH2 : (j >= (0 : Int))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l = (l1 ++ (key :: l4)))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l1)))) (PreH8 : (1 <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (Permutation l1 l0)) (PreH11 : (increasing l0)) (PreH12 : (l0 = (l2 ++ l3))) (PreH13 : (l5 = ((l2 ++ ((Znth ((j + 1)) (l0) (key)) :: l3)) ++ l4))) (PreH14 : ((0 : Int) <= (j + 1))) (PreH15 : ((j + 1) = (Zlength (l2)))) (PreH16 : ((j + 1) <= i)) (PreH17 : ((j + 1) < numsSize_pre)) (PreH18 : (strict_lowerbound key l3)) ,
  (intArray.full nums_pre numsSize_pre l5)
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
|--
  “ ((Znth j l5 (0 : Int)) > key) ” &&
  “ (j >= (0 : Int)) ” &&
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ (l = (l1 ++ (key :: l4))) ” &&
  “ (numsSize_pre = (Zlength (l))) ” &&
  “ (i = (Zlength (l1))) ” &&
  “ (1 <= i) ” &&
  “ (i < numsSize_pre) ” &&
  “ (Permutation l1 l0) ” &&
  “ (increasing l0) ” &&
  “ (l0 = (l2 ++ l3)) ” &&
  “ (l5 = ((l2 ++ ((Znth ((j + 1)) (l0) (key)) :: l3)) ++ l4)) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) = (Zlength (l2))) ” &&
  “ ((j + 1) <= i) ” &&
  “ ((j + 1) < numsSize_pre) ” &&
  “ (strict_lowerbound key l3) ”
  &&  (((nums_pre + (j * sizeof(INT)))) # Int |-> ((Znth j l5 (0 : Int))))
  ** (intArray.missing_i nums_pre j (0 : Int) numsSize_pre l5)
  ** ((returnSize_pre) # Int |-> (numsSize_pre))

noncomputable def sortArray_partial_solve_wit_4 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (l5 : (List Int)) (l2 : (List Int)) (l3 : (List Int)) (l0 : (List Int)) (i : Int) (l1 : (List Int)) (key : Int) (l4 : (List Int)) (PreH1 : ((Znth j l5 (0 : Int)) > key)) (PreH2 : (j >= (0 : Int))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l = (l1 ++ (key :: l4)))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l1)))) (PreH8 : (1 <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (Permutation l1 l0)) (PreH11 : (increasing l0)) (PreH12 : (l0 = (l2 ++ l3))) (PreH13 : (l5 = ((l2 ++ ((Znth ((j + 1)) (l0) (key)) :: l3)) ++ l4))) (PreH14 : ((0 : Int) <= (j + 1))) (PreH15 : ((j + 1) = (Zlength (l2)))) (PreH16 : ((j + 1) <= i)) (PreH17 : ((j + 1) < numsSize_pre)) (PreH18 : (strict_lowerbound key l3)) ,
  (intArray.full nums_pre numsSize_pre l5)
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
|--
  “ ((Znth j l5 (0 : Int)) > key) ” &&
  “ (j >= (0 : Int)) ” &&
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ (l = (l1 ++ (key :: l4))) ” &&
  “ (numsSize_pre = (Zlength (l))) ” &&
  “ (i = (Zlength (l1))) ” &&
  “ (1 <= i) ” &&
  “ (i < numsSize_pre) ” &&
  “ (Permutation l1 l0) ” &&
  “ (increasing l0) ” &&
  “ (l0 = (l2 ++ l3)) ” &&
  “ (l5 = ((l2 ++ ((Znth ((j + 1)) (l0) (key)) :: l3)) ++ l4)) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) = (Zlength (l2))) ” &&
  “ ((j + 1) <= i) ” &&
  “ ((j + 1) < numsSize_pre) ” &&
  “ (strict_lowerbound key l3) ”
  &&  (((nums_pre + ((j + 1) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i nums_pre (j + 1) (0 : Int) numsSize_pre l5)
  ** ((returnSize_pre) # Int |-> (numsSize_pre))

noncomputable def sortArray_partial_solve_wit_5 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (l5 : (List Int)) (l2 : (List Int)) (l3 : (List Int)) (l0 : (List Int)) (i : Int) (l1 : (List Int)) (key : Int) (l4 : (List Int)) (PreH1 : (j < (0 : Int))) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l = (l1 ++ (key :: l4)))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l1)))) (PreH7 : (1 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (Permutation l1 l0)) (PreH10 : (increasing l0)) (PreH11 : (l0 = (l2 ++ l3))) (PreH12 : (l5 = ((l2 ++ ((Znth ((j + 1)) (l0) (key)) :: l3)) ++ l4))) (PreH13 : ((0 : Int) <= (j + 1))) (PreH14 : ((j + 1) = (Zlength (l2)))) (PreH15 : ((j + 1) <= i)) (PreH16 : ((j + 1) < numsSize_pre)) (PreH17 : (strict_lowerbound key l3)) ,
  ((returnSize_pre) # Int |-> (numsSize_pre))
  ** (intArray.full nums_pre numsSize_pre l5)
|--
  “ (j < (0 : Int)) ” &&
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ (l = (l1 ++ (key :: l4))) ” &&
  “ (numsSize_pre = (Zlength (l))) ” &&
  “ (i = (Zlength (l1))) ” &&
  “ (1 <= i) ” &&
  “ (i < numsSize_pre) ” &&
  “ (Permutation l1 l0) ” &&
  “ (increasing l0) ” &&
  “ (l0 = (l2 ++ l3)) ” &&
  “ (l5 = ((l2 ++ ((Znth ((j + 1)) (l0) (key)) :: l3)) ++ l4)) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) = (Zlength (l2))) ” &&
  “ ((j + 1) <= i) ” &&
  “ ((j + 1) < numsSize_pre) ” &&
  “ (strict_lowerbound key l3) ”
  &&  (((nums_pre + ((j + 1) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i nums_pre (j + 1) (0 : Int) numsSize_pre l5)
  ** ((returnSize_pre) # Int |-> (numsSize_pre))

noncomputable def sortArray_partial_solve_wit_6 : Prop :=
  forall (returnSize_pre : Int) (numsSize_pre : Int) (nums_pre : Int) (l : (List Int)) (j : Int) (l5 : (List Int)) (l2 : (List Int)) (l3 : (List Int)) (l0 : (List Int)) (i : Int) (l1 : (List Int)) (key : Int) (l4 : (List Int)) (PreH1 : ((Znth j l5 (0 : Int)) <= key)) (PreH2 : (j >= (0 : Int))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l = (l1 ++ (key :: l4)))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l1)))) (PreH8 : (1 <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (Permutation l1 l0)) (PreH11 : (increasing l0)) (PreH12 : (l0 = (l2 ++ l3))) (PreH13 : (l5 = ((l2 ++ ((Znth ((j + 1)) (l0) (key)) :: l3)) ++ l4))) (PreH14 : ((0 : Int) <= (j + 1))) (PreH15 : ((j + 1) = (Zlength (l2)))) (PreH16 : ((j + 1) <= i)) (PreH17 : ((j + 1) < numsSize_pre)) (PreH18 : (strict_lowerbound key l3)) ,
  (intArray.full nums_pre numsSize_pre l5)
  ** ((returnSize_pre) # Int |-> (numsSize_pre))
|--
  “ ((Znth j l5 (0 : Int)) <= key) ” &&
  “ (j >= (0 : Int)) ” &&
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ (l = (l1 ++ (key :: l4))) ” &&
  “ (numsSize_pre = (Zlength (l))) ” &&
  “ (i = (Zlength (l1))) ” &&
  “ (1 <= i) ” &&
  “ (i < numsSize_pre) ” &&
  “ (Permutation l1 l0) ” &&
  “ (increasing l0) ” &&
  “ (l0 = (l2 ++ l3)) ” &&
  “ (l5 = ((l2 ++ ((Znth ((j + 1)) (l0) (key)) :: l3)) ++ l4)) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) = (Zlength (l2))) ” &&
  “ ((j + 1) <= i) ” &&
  “ ((j + 1) < numsSize_pre) ” &&
  “ (strict_lowerbound key l3) ”
  &&  (((nums_pre + ((j + 1) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i nums_pre (j + 1) (0 : Int) numsSize_pre l5)
  ** ((returnSize_pre) # Int |-> (numsSize_pre))


structure VC_Correct : Type where
  proof_of_sortArray_safety_wit_1 : sortArray_safety_wit_1
  proof_of_sortArray_safety_wit_2 : sortArray_safety_wit_2
  proof_of_sortArray_safety_wit_3 : sortArray_safety_wit_3
  proof_of_sortArray_safety_wit_4 : sortArray_safety_wit_4
  proof_of_sortArray_safety_wit_5 : sortArray_safety_wit_5
  proof_of_sortArray_safety_wit_6 : sortArray_safety_wit_6
  proof_of_sortArray_safety_wit_7 : sortArray_safety_wit_7
  proof_of_sortArray_safety_wit_8 : sortArray_safety_wit_8
  proof_of_sortArray_safety_wit_9 : sortArray_safety_wit_9
  proof_of_sortArray_safety_wit_10 : sortArray_safety_wit_10
  proof_of_sortArray_safety_wit_11 : sortArray_safety_wit_11
  proof_of_sortArray_safety_wit_12 : sortArray_safety_wit_12
  proof_of_sortArray_safety_wit_13 : sortArray_safety_wit_13
  proof_of_sortArray_partial_solve_wit_1 : sortArray_partial_solve_wit_1
  proof_of_sortArray_partial_solve_wit_2 : sortArray_partial_solve_wit_2
  proof_of_sortArray_partial_solve_wit_3 : sortArray_partial_solve_wit_3
  proof_of_sortArray_partial_solve_wit_4 : sortArray_partial_solve_wit_4
  proof_of_sortArray_partial_solve_wit_5 : sortArray_partial_solve_wit_5
  proof_of_sortArray_partial_solve_wit_6 : sortArray_partial_solve_wit_6
  proof_of_sortArray_entail_wit_1 : sortArray_entail_wit_1
  proof_of_sortArray_entail_wit_2 : sortArray_entail_wit_2
  proof_of_sortArray_entail_wit_3 : sortArray_entail_wit_3
  proof_of_sortArray_entail_wit_4_1 : sortArray_entail_wit_4_1
  proof_of_sortArray_entail_wit_4_2 : sortArray_entail_wit_4_2
  proof_of_sortArray_return_wit_1 : sortArray_return_wit_1

end SimpleC.EE.LLM_bench.Algorithms.insertion_sort.insertion_sort_goal
