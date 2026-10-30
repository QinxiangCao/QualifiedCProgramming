import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.majority_element.majority_element_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.majority_element.majority_element_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance majority_element_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def majorityElement_safety_wit_1 : Prop :=
  forall (l : (List Int)) (x : Int) (nums_pre : Int) (numsSize_pre : Int) (PreH1 : (IsMajorityElement x l)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) ,
  ((( &( "vote" ) )) # Int |->_)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** (intArray.full nums_pre numsSize_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def majorityElement_safety_wit_2 : Prop :=
  forall (l : (List Int)) (x : Int) (nums_pre : Int) (numsSize_pre : Int) (PreH1 : (IsMajorityElement x l)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) ,
  ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "vote" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** (intArray.full nums_pre numsSize_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def majorityElement_safety_wit_3 : Prop :=
  forall (l : (List Int)) (x : Int) (nums_pre : Int) (numsSize_pre : Int) (PreH1 : (IsMajorityElement x l)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "candidate" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "vote" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** (intArray.full nums_pre numsSize_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def majorityElement_safety_wit_4 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (numsSize_pre : Int) (candidate : Int) (x : Int) (vote : Int) (i : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (i < numsSize_pre)) (PreH2 : (l = (l1 ++ l2))) (PreH3 : (i = (Zlength (l1)))) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= numsSize_pre)) (PreH6 : (1 <= numsSize_pre)) (PreH7 : (numsSize_pre <= 50000)) (PreH8 : ((0 : Int) <= vote)) (PreH9 : (vote <= i)) (PreH10 : (IsMajorityElement x l)) (PreH11 : (MajorityOnReduced x candidate vote l2)) ,
  ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "vote" ) )) # Int |-> (vote))
  ** ((( &( "candidate" ) )) # Int |-> (candidate))
  ** (intArray.full nums_pre numsSize_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def majorityElement_safety_wit_5 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (numsSize_pre : Int) (candidate : Int) (x : Int) (vote : Int) (i : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (vote = (0 : Int))) (PreH2 : (i < numsSize_pre)) (PreH3 : (l = (l1 ++ l2))) (PreH4 : (i = (Zlength (l1)))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (1 <= numsSize_pre)) (PreH8 : (numsSize_pre <= 50000)) (PreH9 : ((0 : Int) <= vote)) (PreH10 : (vote <= i)) (PreH11 : (IsMajorityElement x l)) (PreH12 : (MajorityOnReduced x candidate vote l2)) ,
  (intArray.full nums_pre numsSize_pre l)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "vote" ) )) # Int |-> (vote))
  ** ((( &( "candidate" ) )) # Int |-> ((Znth i l (0 : Int))))
|--
  “ ((vote + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (vote + 1)) ”

noncomputable def majorityElement_safety_wit_6 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (numsSize_pre : Int) (candidate : Int) (x : Int) (vote : Int) (i : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (vote = (0 : Int))) (PreH2 : (i < numsSize_pre)) (PreH3 : (l = (l1 ++ l2))) (PreH4 : (i = (Zlength (l1)))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (1 <= numsSize_pre)) (PreH8 : (numsSize_pre <= 50000)) (PreH9 : ((0 : Int) <= vote)) (PreH10 : (vote <= i)) (PreH11 : (IsMajorityElement x l)) (PreH12 : (MajorityOnReduced x candidate vote l2)) ,
  (intArray.full nums_pre numsSize_pre l)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "vote" ) )) # Int |-> (vote))
  ** ((( &( "candidate" ) )) # Int |-> ((Znth i l (0 : Int))))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def majorityElement_safety_wit_7 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (numsSize_pre : Int) (candidate : Int) (x : Int) (vote : Int) (i : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : ((Znth i l (0 : Int)) ≠ candidate)) (PreH2 : (vote ≠ (0 : Int))) (PreH3 : (i < numsSize_pre)) (PreH4 : (l = (l1 ++ l2))) (PreH5 : (i = (Zlength (l1)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= numsSize_pre)) (PreH8 : (1 <= numsSize_pre)) (PreH9 : (numsSize_pre <= 50000)) (PreH10 : ((0 : Int) <= vote)) (PreH11 : (vote <= i)) (PreH12 : (IsMajorityElement x l)) (PreH13 : (MajorityOnReduced x candidate vote l2)) ,
  (intArray.full nums_pre numsSize_pre l)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "vote" ) )) # Int |-> (vote))
  ** ((( &( "candidate" ) )) # Int |-> (candidate))
|--
  “ ((vote + (-1)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (vote + (-1))) ”

noncomputable def majorityElement_safety_wit_8 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (numsSize_pre : Int) (candidate : Int) (x : Int) (vote : Int) (i : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : ((Znth i l (0 : Int)) = candidate)) (PreH2 : (vote ≠ (0 : Int))) (PreH3 : (i < numsSize_pre)) (PreH4 : (l = (l1 ++ l2))) (PreH5 : (i = (Zlength (l1)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= numsSize_pre)) (PreH8 : (1 <= numsSize_pre)) (PreH9 : (numsSize_pre <= 50000)) (PreH10 : ((0 : Int) <= vote)) (PreH11 : (vote <= i)) (PreH12 : (IsMajorityElement x l)) (PreH13 : (MajorityOnReduced x candidate vote l2)) ,
  (intArray.full nums_pre numsSize_pre l)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "vote" ) )) # Int |-> (vote))
  ** ((( &( "candidate" ) )) # Int |-> (candidate))
|--
  “ ((vote + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (vote + 1)) ”

noncomputable def majorityElement_safety_wit_9 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (numsSize_pre : Int) (candidate : Int) (x : Int) (vote : Int) (i : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : ((Znth i l (0 : Int)) = candidate)) (PreH2 : (vote ≠ (0 : Int))) (PreH3 : (i < numsSize_pre)) (PreH4 : (l = (l1 ++ l2))) (PreH5 : (i = (Zlength (l1)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= numsSize_pre)) (PreH8 : (1 <= numsSize_pre)) (PreH9 : (numsSize_pre <= 50000)) (PreH10 : ((0 : Int) <= vote)) (PreH11 : (vote <= i)) (PreH12 : (IsMajorityElement x l)) (PreH13 : (MajorityOnReduced x candidate vote l2)) ,
  (intArray.full nums_pre numsSize_pre l)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "vote" ) )) # Int |-> (vote))
  ** ((( &( "candidate" ) )) # Int |-> (candidate))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def majorityElement_safety_wit_10 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (numsSize_pre : Int) (candidate : Int) (x : Int) (vote : Int) (i : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : ((Znth i l (0 : Int)) ≠ candidate)) (PreH2 : (vote ≠ (0 : Int))) (PreH3 : (i < numsSize_pre)) (PreH4 : (l = (l1 ++ l2))) (PreH5 : (i = (Zlength (l1)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= numsSize_pre)) (PreH8 : (1 <= numsSize_pre)) (PreH9 : (numsSize_pre <= 50000)) (PreH10 : ((0 : Int) <= vote)) (PreH11 : (vote <= i)) (PreH12 : (IsMajorityElement x l)) (PreH13 : (MajorityOnReduced x candidate vote l2)) ,
  (intArray.full nums_pre numsSize_pre l)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "vote" ) )) # Int |-> (vote))
  ** ((( &( "candidate" ) )) # Int |-> (candidate))
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def majorityElement_safety_wit_11 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (numsSize_pre : Int) (candidate : Int) (x : Int) (vote : Int) (i : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : ((Znth i l (0 : Int)) ≠ candidate)) (PreH2 : (vote ≠ (0 : Int))) (PreH3 : (i < numsSize_pre)) (PreH4 : (l = (l1 ++ l2))) (PreH5 : (i = (Zlength (l1)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= numsSize_pre)) (PreH8 : (1 <= numsSize_pre)) (PreH9 : (numsSize_pre <= 50000)) (PreH10 : ((0 : Int) <= vote)) (PreH11 : (vote <= i)) (PreH12 : (IsMajorityElement x l)) (PreH13 : (MajorityOnReduced x candidate vote l2)) ,
  (intArray.full nums_pre numsSize_pre l)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "vote" ) )) # Int |-> (vote))
  ** ((( &( "candidate" ) )) # Int |-> (candidate))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def majorityElement_safety_wit_12 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (numsSize_pre : Int) (candidate : Int) (x : Int) (vote : Int) (i : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (vote = (0 : Int))) (PreH2 : (i < numsSize_pre)) (PreH3 : (l = (l1 ++ l2))) (PreH4 : (i = (Zlength (l1)))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (1 <= numsSize_pre)) (PreH8 : (numsSize_pre <= 50000)) (PreH9 : ((0 : Int) <= vote)) (PreH10 : (vote <= i)) (PreH11 : (IsMajorityElement x l)) (PreH12 : (MajorityOnReduced x candidate vote l2)) ,
  (intArray.full nums_pre numsSize_pre l)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "vote" ) )) # Int |-> ((vote + 1)))
  ** ((( &( "candidate" ) )) # Int |-> ((Znth i l (0 : Int))))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def majorityElement_safety_wit_13 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (numsSize_pre : Int) (candidate : Int) (x : Int) (vote : Int) (i : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : ((Znth i l (0 : Int)) = candidate)) (PreH2 : (vote ≠ (0 : Int))) (PreH3 : (i < numsSize_pre)) (PreH4 : (l = (l1 ++ l2))) (PreH5 : (i = (Zlength (l1)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= numsSize_pre)) (PreH8 : (1 <= numsSize_pre)) (PreH9 : (numsSize_pre <= 50000)) (PreH10 : ((0 : Int) <= vote)) (PreH11 : (vote <= i)) (PreH12 : (IsMajorityElement x l)) (PreH13 : (MajorityOnReduced x candidate vote l2)) ,
  (intArray.full nums_pre numsSize_pre l)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "vote" ) )) # Int |-> ((vote + 1)))
  ** ((( &( "candidate" ) )) # Int |-> (candidate))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def majorityElement_safety_wit_14 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (numsSize_pre : Int) (candidate : Int) (x : Int) (vote : Int) (i : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : ((Znth i l (0 : Int)) ≠ candidate)) (PreH2 : (vote ≠ (0 : Int))) (PreH3 : (i < numsSize_pre)) (PreH4 : (l = (l1 ++ l2))) (PreH5 : (i = (Zlength (l1)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= numsSize_pre)) (PreH8 : (1 <= numsSize_pre)) (PreH9 : (numsSize_pre <= 50000)) (PreH10 : ((0 : Int) <= vote)) (PreH11 : (vote <= i)) (PreH12 : (IsMajorityElement x l)) (PreH13 : (MajorityOnReduced x candidate vote l2)) ,
  (intArray.full nums_pre numsSize_pre l)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "vote" ) )) # Int |-> ((vote + (-1))))
  ** ((( &( "candidate" ) )) # Int |-> (candidate))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def majorityElement_entail_wit_1 : Prop :=
  (
forall (l : (List Int)) (x_2 : Int) (nums_pre : Int) (numsSize_pre : Int) (PreH1 : (IsMajorityElement x_2 l)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) ,
  (intArray.full nums_pre numsSize_pre l)
|--
  EX x : Int, EX l1 : (List Int), EX l2 : (List Int),
  “ (l = (l1 ++ l2)) ” &&
  “ ((0 : Int) = (Zlength (l1))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= numsSize_pre) ” &&
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ (IsMajorityElement x l) ” &&
  “ (MajorityOnReduced x (0 : Int) (0 : Int) l2) ”
  &&  (intArray.full nums_pre numsSize_pre l)
) \/
(
forall (l : (List Int)) (x_2 : Int) (numsSize_pre : Int) (PreH1 : (IsMajorityElement x_2 l)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) ,
  TT && emp 
|--
  EX x : Int, EX l1 : (List Int), EX l2 : (List Int),
  “ (l = (l1 ++ l2)) ” &&
  “ ((0 : Int) = (Zlength (l1))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (Zlength (l))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ (IsMajorityElement x l) ” &&
  “ (MajorityOnReduced x (0 : Int) (0 : Int) l2) ”
  &&  emp
)

noncomputable def majorityElement_entail_wit_2_1 : Prop :=
  (
forall (l : (List Int)) (nums_pre : Int) (numsSize_pre : Int) (candidate : Int) (x_2 : Int) (vote : Int) (i : Int) (l1_2 : (List Int)) (l2_2 : (List Int)) (PreH1 : (vote = (0 : Int))) (PreH2 : (i < numsSize_pre)) (PreH3 : (l = (l1_2 ++ l2_2))) (PreH4 : (i = (Zlength (l1_2)))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (1 <= numsSize_pre)) (PreH8 : (numsSize_pre <= 50000)) (PreH9 : ((0 : Int) <= vote)) (PreH10 : (vote <= i)) (PreH11 : (IsMajorityElement x_2 l)) (PreH12 : (MajorityOnReduced x_2 candidate vote l2_2)) ,
  (intArray.full nums_pre numsSize_pre l)
|--
  EX x : Int, EX l1 : (List Int), EX l2 : (List Int),
  “ (l = (l1 ++ l2)) ” &&
  “ ((i + 1) = (Zlength (l1))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= numsSize_pre) ” &&
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ ((0 : Int) <= (vote + 1)) ” &&
  “ ((vote + 1) <= (i + 1)) ” &&
  “ (IsMajorityElement x l) ” &&
  “ (MajorityOnReduced x (Znth i l (0 : Int)) (vote + 1) l2) ”
  &&  (intArray.full nums_pre numsSize_pre l)
) \/
(
forall (l : (List Int)) (numsSize_pre : Int) (candidate : Int) (x_2 : Int) (vote : Int) (i : Int) (l1_2 : (List Int)) (l2_2 : (List Int)) (PreH1 : (vote = (0 : Int))) (PreH2 : (i < numsSize_pre)) (PreH3 : (l = (l1_2 ++ l2_2))) (PreH4 : (i = (Zlength (l1_2)))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (1 <= numsSize_pre)) (PreH8 : (numsSize_pre <= 50000)) (PreH9 : ((0 : Int) <= vote)) (PreH10 : (vote <= i)) (PreH11 : (IsMajorityElement x_2 l)) (PreH12 : (MajorityOnReduced x_2 candidate vote l2_2)) ,
  TT && emp 
|--
  EX x : Int, EX l1 : (List Int), EX l2 : (List Int),
  “ ((l1_2 ++ l2_2) = (l1 ++ l2)) ” &&
  “ (((Zlength (l1_2)) + 1) = (Zlength (l1))) ” &&
  “ ((0 : Int) <= ((Zlength (l1_2)) + 1)) ” &&
  “ (((Zlength (l1_2)) + 1) <= numsSize_pre) ” &&
  “ ((0 : Int) <= ((0 : Int) + 1)) ” &&
  “ (((0 : Int) + 1) <= ((Zlength (l1_2)) + 1)) ” &&
  “ (IsMajorityElement x (l1_2 ++ l2_2)) ” &&
  “ (MajorityOnReduced x (Znth (Zlength (l1_2)) (l1_2 ++ l2_2) (0 : Int)) ((0 : Int) + 1) l2) ”
  &&  emp
)

noncomputable def majorityElement_entail_wit_2_2 : Prop :=
  (
forall (l : (List Int)) (nums_pre : Int) (numsSize_pre : Int) (candidate : Int) (x_2 : Int) (vote : Int) (i : Int) (l1_2 : (List Int)) (l2_2 : (List Int)) (PreH1 : ((Znth i l (0 : Int)) = candidate)) (PreH2 : (vote ≠ (0 : Int))) (PreH3 : (i < numsSize_pre)) (PreH4 : (l = (l1_2 ++ l2_2))) (PreH5 : (i = (Zlength (l1_2)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= numsSize_pre)) (PreH8 : (1 <= numsSize_pre)) (PreH9 : (numsSize_pre <= 50000)) (PreH10 : ((0 : Int) <= vote)) (PreH11 : (vote <= i)) (PreH12 : (IsMajorityElement x_2 l)) (PreH13 : (MajorityOnReduced x_2 candidate vote l2_2)) ,
  (intArray.full nums_pre numsSize_pre l)
|--
  EX x : Int, EX l1 : (List Int), EX l2 : (List Int),
  “ (l = (l1 ++ l2)) ” &&
  “ ((i + 1) = (Zlength (l1))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= numsSize_pre) ” &&
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ ((0 : Int) <= (vote + 1)) ” &&
  “ ((vote + 1) <= (i + 1)) ” &&
  “ (IsMajorityElement x l) ” &&
  “ (MajorityOnReduced x candidate (vote + 1) l2) ”
  &&  (intArray.full nums_pre numsSize_pre l)
) \/
(
forall (l : (List Int)) (numsSize_pre : Int) (candidate : Int) (x_2 : Int) (vote : Int) (i : Int) (l1_2 : (List Int)) (l2_2 : (List Int)) (PreH1 : ((Znth i l (0 : Int)) = candidate)) (PreH2 : (vote ≠ (0 : Int))) (PreH3 : (i < numsSize_pre)) (PreH4 : (l = (l1_2 ++ l2_2))) (PreH5 : (i = (Zlength (l1_2)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= numsSize_pre)) (PreH8 : (1 <= numsSize_pre)) (PreH9 : (numsSize_pre <= 50000)) (PreH10 : ((0 : Int) <= vote)) (PreH11 : (vote <= i)) (PreH12 : (IsMajorityElement x_2 l)) (PreH13 : (MajorityOnReduced x_2 candidate vote l2_2)) ,
  TT && emp 
|--
  EX x : Int, EX l1 : (List Int), EX l2 : (List Int),
  “ ((l1_2 ++ l2_2) = (l1 ++ l2)) ” &&
  “ (((Zlength (l1_2)) + 1) = (Zlength (l1))) ” &&
  “ ((0 : Int) <= ((Zlength (l1_2)) + 1)) ” &&
  “ (((Zlength (l1_2)) + 1) <= numsSize_pre) ” &&
  “ ((0 : Int) <= (vote + 1)) ” &&
  “ ((vote + 1) <= ((Zlength (l1_2)) + 1)) ” &&
  “ (IsMajorityElement x (l1_2 ++ l2_2)) ” &&
  “ (MajorityOnReduced x (Znth (Zlength (l1_2)) (l1_2 ++ l2_2) (0 : Int)) (vote + 1) l2) ”
  &&  emp
)

noncomputable def majorityElement_entail_wit_2_3 : Prop :=
  (
forall (l : (List Int)) (nums_pre : Int) (numsSize_pre : Int) (candidate : Int) (x_2 : Int) (vote : Int) (i : Int) (l1_2 : (List Int)) (l2_2 : (List Int)) (PreH1 : ((Znth i l (0 : Int)) ≠ candidate)) (PreH2 : (vote ≠ (0 : Int))) (PreH3 : (i < numsSize_pre)) (PreH4 : (l = (l1_2 ++ l2_2))) (PreH5 : (i = (Zlength (l1_2)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= numsSize_pre)) (PreH8 : (1 <= numsSize_pre)) (PreH9 : (numsSize_pre <= 50000)) (PreH10 : ((0 : Int) <= vote)) (PreH11 : (vote <= i)) (PreH12 : (IsMajorityElement x_2 l)) (PreH13 : (MajorityOnReduced x_2 candidate vote l2_2)) ,
  (intArray.full nums_pre numsSize_pre l)
|--
  EX x : Int, EX l1 : (List Int), EX l2 : (List Int),
  “ (l = (l1 ++ l2)) ” &&
  “ ((i + 1) = (Zlength (l1))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= numsSize_pre) ” &&
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ ((0 : Int) <= (vote + (-1))) ” &&
  “ ((vote + (-1)) <= (i + 1)) ” &&
  “ (IsMajorityElement x l) ” &&
  “ (MajorityOnReduced x candidate (vote + (-1)) l2) ”
  &&  (intArray.full nums_pre numsSize_pre l)
) \/
(
forall (l : (List Int)) (numsSize_pre : Int) (candidate : Int) (x_2 : Int) (vote : Int) (i : Int) (l1_2 : (List Int)) (l2_2 : (List Int)) (PreH1 : ((Znth i l (0 : Int)) ≠ candidate)) (PreH2 : (vote ≠ (0 : Int))) (PreH3 : (i < numsSize_pre)) (PreH4 : (l = (l1_2 ++ l2_2))) (PreH5 : (i = (Zlength (l1_2)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= numsSize_pre)) (PreH8 : (1 <= numsSize_pre)) (PreH9 : (numsSize_pre <= 50000)) (PreH10 : ((0 : Int) <= vote)) (PreH11 : (vote <= i)) (PreH12 : (IsMajorityElement x_2 l)) (PreH13 : (MajorityOnReduced x_2 candidate vote l2_2)) ,
  TT && emp 
|--
  EX x : Int, EX l1 : (List Int), EX l2 : (List Int),
  “ ((l1_2 ++ l2_2) = (l1 ++ l2)) ” &&
  “ (((Zlength (l1_2)) + 1) = (Zlength (l1))) ” &&
  “ ((0 : Int) <= ((Zlength (l1_2)) + 1)) ” &&
  “ (((Zlength (l1_2)) + 1) <= numsSize_pre) ” &&
  “ ((0 : Int) <= (vote + (-1))) ” &&
  “ ((vote + (-1)) <= ((Zlength (l1_2)) + 1)) ” &&
  “ (IsMajorityElement x (l1_2 ++ l2_2)) ” &&
  “ (MajorityOnReduced x candidate (vote + (-1)) l2) ”
  &&  emp
)

noncomputable def majorityElement_return_wit_1 : Prop :=
  (
forall (l : (List Int)) (nums_pre : Int) (numsSize_pre : Int) (candidate : Int) (x : Int) (vote : Int) (i : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (i >= numsSize_pre)) (PreH2 : (l = (l1 ++ l2))) (PreH3 : (i = (Zlength (l1)))) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= numsSize_pre)) (PreH6 : (1 <= numsSize_pre)) (PreH7 : (numsSize_pre <= 50000)) (PreH8 : ((0 : Int) <= vote)) (PreH9 : (vote <= i)) (PreH10 : (IsMajorityElement x l)) (PreH11 : (MajorityOnReduced x candidate vote l2)) ,
  (intArray.full nums_pre numsSize_pre l)
|--
  “ (IsMajorityElement candidate l) ”
  &&  (intArray.full nums_pre numsSize_pre l)
) \/
(
forall (l : (List Int)) (numsSize_pre : Int) (candidate : Int) (x : Int) (vote : Int) (i : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (i >= numsSize_pre)) (PreH2 : (l = (l1 ++ l2))) (PreH3 : (i = (Zlength (l1)))) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= numsSize_pre)) (PreH6 : (1 <= numsSize_pre)) (PreH7 : (numsSize_pre <= 50000)) (PreH8 : ((0 : Int) <= vote)) (PreH9 : (vote <= i)) (PreH10 : (IsMajorityElement x l)) (PreH11 : (MajorityOnReduced x candidate vote l2)) ,
  TT && emp 
|--
  “ (IsMajorityElement candidate l) ”
  &&  emp
)

noncomputable def majorityElement_return_wit_1_split_goal_1 : Prop :=
  forall (l : (List Int)) (numsSize_pre : Int) (candidate : Int) (x : Int) (vote : Int) (i : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (i >= numsSize_pre)) (PreH2 : (l = (l1 ++ l2))) (PreH3 : (i = (Zlength (l1)))) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= numsSize_pre)) (PreH6 : (1 <= numsSize_pre)) (PreH7 : (numsSize_pre <= 50000)) (PreH8 : ((0 : Int) <= vote)) (PreH9 : (vote <= i)) (PreH10 : (IsMajorityElement x l)) (PreH11 : (MajorityOnReduced x candidate vote l2)) ,
  (IsMajorityElement candidate l)

noncomputable def majorityElement_partial_solve_wit_1 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (numsSize_pre : Int) (candidate : Int) (x : Int) (vote : Int) (i : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (vote = (0 : Int))) (PreH2 : (i < numsSize_pre)) (PreH3 : (l = (l1 ++ l2))) (PreH4 : (i = (Zlength (l1)))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (1 <= numsSize_pre)) (PreH8 : (numsSize_pre <= 50000)) (PreH9 : ((0 : Int) <= vote)) (PreH10 : (vote <= i)) (PreH11 : (IsMajorityElement x l)) (PreH12 : (MajorityOnReduced x candidate vote l2)) ,
  (intArray.full nums_pre numsSize_pre l)
|--
  “ (vote = (0 : Int)) ” &&
  “ (i < numsSize_pre) ” &&
  “ (l = (l1 ++ l2)) ” &&
  “ (i = (Zlength (l1))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= numsSize_pre) ” &&
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ ((0 : Int) <= vote) ” &&
  “ (vote <= i) ” &&
  “ (IsMajorityElement x l) ” &&
  “ (MajorityOnReduced x candidate vote l2) ”
  &&  (((nums_pre + (i * sizeof(INT)))) # Int |-> ((Znth i l (0 : Int))))
  ** (intArray.missing_i nums_pre i (0 : Int) numsSize_pre l)

noncomputable def majorityElement_partial_solve_wit_2 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (numsSize_pre : Int) (candidate : Int) (x : Int) (vote : Int) (i : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (vote = (0 : Int))) (PreH2 : (i < numsSize_pre)) (PreH3 : (l = (l1 ++ l2))) (PreH4 : (i = (Zlength (l1)))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (1 <= numsSize_pre)) (PreH8 : (numsSize_pre <= 50000)) (PreH9 : ((0 : Int) <= vote)) (PreH10 : (vote <= i)) (PreH11 : (IsMajorityElement x l)) (PreH12 : (MajorityOnReduced x candidate vote l2)) ,
  (intArray.full nums_pre numsSize_pre l)
|--
  “ (vote = (0 : Int)) ” &&
  “ (i < numsSize_pre) ” &&
  “ (l = (l1 ++ l2)) ” &&
  “ (i = (Zlength (l1))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= numsSize_pre) ” &&
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ ((0 : Int) <= vote) ” &&
  “ (vote <= i) ” &&
  “ (IsMajorityElement x l) ” &&
  “ (MajorityOnReduced x candidate vote l2) ”
  &&  (((nums_pre + (i * sizeof(INT)))) # Int |-> ((Znth i l (0 : Int))))
  ** (intArray.missing_i nums_pre i (0 : Int) numsSize_pre l)

noncomputable def majorityElement_partial_solve_wit_3 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (numsSize_pre : Int) (candidate : Int) (x : Int) (vote : Int) (i : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (vote ≠ (0 : Int))) (PreH2 : (i < numsSize_pre)) (PreH3 : (l = (l1 ++ l2))) (PreH4 : (i = (Zlength (l1)))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (1 <= numsSize_pre)) (PreH8 : (numsSize_pre <= 50000)) (PreH9 : ((0 : Int) <= vote)) (PreH10 : (vote <= i)) (PreH11 : (IsMajorityElement x l)) (PreH12 : (MajorityOnReduced x candidate vote l2)) ,
  (intArray.full nums_pre numsSize_pre l)
|--
  “ (vote ≠ (0 : Int)) ” &&
  “ (i < numsSize_pre) ” &&
  “ (l = (l1 ++ l2)) ” &&
  “ (i = (Zlength (l1))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= numsSize_pre) ” &&
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ ((0 : Int) <= vote) ” &&
  “ (vote <= i) ” &&
  “ (IsMajorityElement x l) ” &&
  “ (MajorityOnReduced x candidate vote l2) ”
  &&  (((nums_pre + (i * sizeof(INT)))) # Int |-> ((Znth i l (0 : Int))))
  ** (intArray.missing_i nums_pre i (0 : Int) numsSize_pre l)


structure VC_Correct : Type where
  proof_of_majorityElement_safety_wit_1 : majorityElement_safety_wit_1
  proof_of_majorityElement_safety_wit_2 : majorityElement_safety_wit_2
  proof_of_majorityElement_safety_wit_3 : majorityElement_safety_wit_3
  proof_of_majorityElement_safety_wit_4 : majorityElement_safety_wit_4
  proof_of_majorityElement_safety_wit_5 : majorityElement_safety_wit_5
  proof_of_majorityElement_safety_wit_6 : majorityElement_safety_wit_6
  proof_of_majorityElement_safety_wit_7 : majorityElement_safety_wit_7
  proof_of_majorityElement_safety_wit_8 : majorityElement_safety_wit_8
  proof_of_majorityElement_safety_wit_9 : majorityElement_safety_wit_9
  proof_of_majorityElement_safety_wit_10 : majorityElement_safety_wit_10
  proof_of_majorityElement_safety_wit_11 : majorityElement_safety_wit_11
  proof_of_majorityElement_safety_wit_12 : majorityElement_safety_wit_12
  proof_of_majorityElement_safety_wit_13 : majorityElement_safety_wit_13
  proof_of_majorityElement_safety_wit_14 : majorityElement_safety_wit_14
  proof_of_majorityElement_partial_solve_wit_1 : majorityElement_partial_solve_wit_1
  proof_of_majorityElement_partial_solve_wit_2 : majorityElement_partial_solve_wit_2
  proof_of_majorityElement_partial_solve_wit_3 : majorityElement_partial_solve_wit_3
  proof_of_majorityElement_entail_wit_1 : majorityElement_entail_wit_1
  proof_of_majorityElement_entail_wit_2_1 : majorityElement_entail_wit_2_1
  proof_of_majorityElement_entail_wit_2_2 : majorityElement_entail_wit_2_2
  proof_of_majorityElement_entail_wit_2_3 : majorityElement_entail_wit_2_3
  proof_of_majorityElement_return_wit_1 : majorityElement_return_wit_1

end SimpleC.EE.LLM_bench.Algorithms.majority_element.majority_element_goal
