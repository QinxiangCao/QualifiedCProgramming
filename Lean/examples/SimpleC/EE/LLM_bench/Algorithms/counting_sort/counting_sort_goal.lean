import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.counting_sort.counting_sort_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.counting_sort.counting_sort_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance counting_sort_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def sort_safety_wit_1 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH5 : (Forall ((GT.gt (α := Int)) (100)) input)) ,
  ((( &( "value" ) )) # Int |->_)
  ** (intArray.undef_full ( &( "output" ) ) 100)
  ** (intArray.undef_full ( &( "count" ) ) 100)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre input)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def sort_safety_wit_2 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (value : Int) (count_mixed : (List (Option Int))) (output_mixed : (List (Option Int))) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (output_mixed)) = 100)) (PreH5 : ((Zlength (count_mixed)) = 100)) (PreH6 : ((0 : Int) <= value)) (PreH7 : (value <= 100)) (PreH8 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH9 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH10 : (Forall (Eq (None)) output_mixed)) (PreH11 : (CountingZeroedPrefix count_mixed value)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
  ** (intArray.mixed_full ( &( "count" ) ) 100 count_mixed)
|--
  “ (100 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 100) ”

noncomputable def sort_safety_wit_3 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (value : Int) (count_mixed : (List (Option Int))) (output_mixed : (List (Option Int))) (PreH1 : (value < 100)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed)) = 100)) (PreH6 : ((Zlength (count_mixed)) = 100)) (PreH7 : ((0 : Int) <= value)) (PreH8 : (value <= 100)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall (Eq (None)) output_mixed)) (PreH12 : (CountingZeroedPrefix count_mixed value)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
  ** (intArray.mixed_full ( &( "count" ) ) 100 count_mixed)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def sort_safety_wit_4 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (value : Int) (count_mixed : (List (Option Int))) (output_mixed : (List (Option Int))) (PreH1 : (value < 100)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed)) = 100)) (PreH6 : ((Zlength (count_mixed)) = 100)) (PreH7 : ((0 : Int) <= value)) (PreH8 : (value <= 100)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall (Eq (None)) output_mixed)) (PreH12 : (CountingZeroedPrefix count_mixed value)) ,
  (intArray.mixed_full ( &( "count" ) ) 100 (replace_Znth (value) ((Some ((0 : Int)))) (count_mixed)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
|--
  “ ((value + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (value + 1)) ”

noncomputable def sort_safety_wit_5 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (value : Int) (count_mixed : (List (Option Int))) (output_mixed : (List (Option Int))) (PreH1 : (value >= 100)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed)) = 100)) (PreH6 : ((Zlength (count_mixed)) = 100)) (PreH7 : ((0 : Int) <= value)) (PreH8 : (value <= 100)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall (Eq (None)) output_mixed)) (PreH12 : (CountingZeroedPrefix count_mixed value)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
  ** (intArray.mixed_full ( &( "count" ) ) 100 count_mixed)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def sort_safety_wit_6 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (i : Int) (output_mixed : (List (Option Int))) (counts : (List Int)) (PreH1 : ((0 : Int) <= (Znth i input (0 : Int)))) (PreH2 : ((Znth i input (0 : Int)) < 100)) (PreH3 : ((0 : Int) <= (Znth (Znth i input (0 : Int)) counts (0 : Int)))) (PreH4 : ((Znth (Znth i input (0 : Int)) counts (0 : Int)) < 100)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((Zlength (input)) = n_pre)) (PreH11 : ((Zlength (output_mixed)) = 100)) (PreH12 : ((Zlength (counts)) = 100)) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH16 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH17 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts)) (PreH18 : (Forall ((GE.ge (α := Int)) (i)) counts)) (PreH19 : (Forall (Eq (None)) output_mixed)) (PreH20 : (CountingHistogramPrefix input counts i)) ,
  (intArray.full ( &( "count" ) ) 100 counts)
  ** (intArray.full a_pre n_pre input)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
|--
  “ (((Znth (Znth i input (0 : Int)) counts (0 : Int)) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth (Znth i input (0 : Int)) counts (0 : Int)) + 1)) ”

noncomputable def sort_safety_wit_7 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (i : Int) (output_mixed : (List (Option Int))) (counts : (List Int)) (PreH1 : ((0 : Int) <= (Znth i input (0 : Int)))) (PreH2 : ((Znth i input (0 : Int)) < 100)) (PreH3 : ((0 : Int) <= (Znth (Znth i input (0 : Int)) counts (0 : Int)))) (PreH4 : ((Znth (Znth i input (0 : Int)) counts (0 : Int)) < 100)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((Zlength (input)) = n_pre)) (PreH11 : ((Zlength (output_mixed)) = 100)) (PreH12 : ((Zlength (counts)) = 100)) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH16 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH17 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts)) (PreH18 : (Forall ((GE.ge (α := Int)) (i)) counts)) (PreH19 : (Forall (Eq (None)) output_mixed)) (PreH20 : (CountingHistogramPrefix input counts i)) ,
  (intArray.full ( &( "count" ) ) 100 (replace_Znth ((Znth i input (0 : Int))) (((Znth (Znth i input (0 : Int)) counts (0 : Int)) + 1)) (counts)))
  ** (intArray.full a_pre n_pre input)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def sort_safety_wit_8 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (i : Int) (counts : (List Int)) (output_mixed : (List (Option Int))) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed)) = 100)) (PreH6 : ((Zlength (counts)) = 100)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts)) (PreH12 : (Forall ((GE.ge (α := Int)) (i)) counts)) (PreH13 : (Forall (Eq (None)) output_mixed)) (PreH14 : (CountingHistogramPrefix input counts i)) ,
  ((( &( "value" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
  ** (intArray.full ( &( "count" ) ) 100 counts)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def sort_safety_wit_9 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (value : Int) (positions : (List Int)) (output_mixed : (List (Option Int))) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (output_mixed)) = 100)) (PreH5 : ((Zlength (positions)) = 100)) (PreH6 : (1 <= value)) (PreH7 : (value <= 100)) (PreH8 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH9 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions)) (PreH11 : (Forall ((GE.ge (α := Int)) (n_pre)) positions)) (PreH12 : ((value < 100) -> (((Znth value positions (0 : Int)) + (Znth (value - 1) positions (0 : Int))) <= n_pre))) (PreH13 : (Forall (Eq (None)) output_mixed)) (PreH14 : (CountingCumulativeState input positions value)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
  ** (intArray.full ( &( "count" ) ) 100 positions)
|--
  “ (100 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 100) ”

noncomputable def sort_safety_wit_10 : Prop :=
  (
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (value : Int) (positions : (List Int)) (output_mixed : (List (Option Int))) (PreH1 : (value < 100)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed)) = 100)) (PreH6 : ((Zlength (positions)) = 100)) (PreH7 : (1 <= value)) (PreH8 : (value <= 100)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions)) (PreH12 : (Forall ((GE.ge (α := Int)) (n_pre)) positions)) (PreH13 : ((value < 100) -> (((Znth value positions (0 : Int)) + (Znth (value - 1) positions (0 : Int))) <= n_pre))) (PreH14 : (Forall (Eq (None)) output_mixed)) (PreH15 : (CountingCumulativeState input positions value)) ,
  (intArray.full ( &( "count" ) ) 100 positions)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
|--
  “ (((Znth value positions (0 : Int)) + (Znth (value - 1) positions (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth value positions (0 : Int)) + (Znth (value - 1) positions (0 : Int)))) ”
) \/
(
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (value : Int) (positions : (List Int)) (output_mixed : (List (Option Int))) (PreH1 : (value < 100)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed)) = 100)) (PreH6 : ((Zlength (positions)) = 100)) (PreH7 : (1 <= value)) (PreH8 : (value <= 100)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions)) (PreH12 : (Forall ((GE.ge (α := Int)) (n_pre)) positions)) (PreH13 : ((value < 100) -> (((Znth value positions (0 : Int)) + (Znth (value - 1) positions (0 : Int))) <= n_pre))) (PreH14 : (Forall (Eq (None)) output_mixed)) (PreH15 : (CountingCumulativeState input positions value)) ,
  (intArray.full ( &( "count" ) ) 100 positions)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
|--
  “ (((Znth value positions (0 : Int)) + (Znth (value - 1) positions (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth value positions (0 : Int)) + (Znth (value - 1) positions (0 : Int)))) ”
)

noncomputable def sort_safety_wit_10_split_goal_1 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (value : Int) (positions : (List Int)) (output_mixed : (List (Option Int))) (PreH1 : (value < 100)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed)) = 100)) (PreH6 : ((Zlength (positions)) = 100)) (PreH7 : (1 <= value)) (PreH8 : (value <= 100)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions)) (PreH12 : (Forall ((GE.ge (α := Int)) (n_pre)) positions)) (PreH13 : ((value < 100) -> (((Znth value positions (0 : Int)) + (Znth (value - 1) positions (0 : Int))) <= n_pre))) (PreH14 : (Forall (Eq (None)) output_mixed)) (PreH15 : (CountingCumulativeState input positions value)) ,
  (intArray.full ( &( "count" ) ) 100 positions)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
|--
  “ (((Znth value positions (0 : Int)) + (Znth (value - 1) positions (0 : Int))) <= INT_MAX) ”

noncomputable def sort_safety_wit_10_split_goal_2 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (value : Int) (positions : (List Int)) (output_mixed : (List (Option Int))) (PreH1 : (value < 100)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed)) = 100)) (PreH6 : ((Zlength (positions)) = 100)) (PreH7 : (1 <= value)) (PreH8 : (value <= 100)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions)) (PreH12 : (Forall ((GE.ge (α := Int)) (n_pre)) positions)) (PreH13 : ((value < 100) -> (((Znth value positions (0 : Int)) + (Znth (value - 1) positions (0 : Int))) <= n_pre))) (PreH14 : (Forall (Eq (None)) output_mixed)) (PreH15 : (CountingCumulativeState input positions value)) ,
  (intArray.full ( &( "count" ) ) 100 positions)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
|--
  “ ((INT_MIN) <= ((Znth value positions (0 : Int)) + (Znth (value - 1) positions (0 : Int)))) ”

noncomputable def sort_safety_wit_11 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (value : Int) (positions : (List Int)) (output_mixed : (List (Option Int))) (PreH1 : (value < 100)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed)) = 100)) (PreH6 : ((Zlength (positions)) = 100)) (PreH7 : (1 <= value)) (PreH8 : (value <= 100)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions)) (PreH12 : (Forall ((GE.ge (α := Int)) (n_pre)) positions)) (PreH13 : ((value < 100) -> (((Znth value positions (0 : Int)) + (Znth (value - 1) positions (0 : Int))) <= n_pre))) (PreH14 : (Forall (Eq (None)) output_mixed)) (PreH15 : (CountingCumulativeState input positions value)) ,
  (intArray.full ( &( "count" ) ) 100 positions)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
|--
  “ ((value - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (value - 1)) ”

noncomputable def sort_safety_wit_12 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (value : Int) (positions : (List Int)) (output_mixed : (List (Option Int))) (PreH1 : (value < 100)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed)) = 100)) (PreH6 : ((Zlength (positions)) = 100)) (PreH7 : (1 <= value)) (PreH8 : (value <= 100)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions)) (PreH12 : (Forall ((GE.ge (α := Int)) (n_pre)) positions)) (PreH13 : ((value < 100) -> (((Znth value positions (0 : Int)) + (Znth (value - 1) positions (0 : Int))) <= n_pre))) (PreH14 : (Forall (Eq (None)) output_mixed)) (PreH15 : (CountingCumulativeState input positions value)) ,
  (intArray.full ( &( "count" ) ) 100 positions)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def sort_safety_wit_13 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (value : Int) (positions : (List Int)) (output_mixed : (List (Option Int))) (PreH1 : (value < 100)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed)) = 100)) (PreH6 : ((Zlength (positions)) = 100)) (PreH7 : (1 <= value)) (PreH8 : (value <= 100)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions)) (PreH12 : (Forall ((GE.ge (α := Int)) (n_pre)) positions)) (PreH13 : ((value < 100) -> (((Znth value positions (0 : Int)) + (Znth (value - 1) positions (0 : Int))) <= n_pre))) (PreH14 : (Forall (Eq (None)) output_mixed)) (PreH15 : (CountingCumulativeState input positions value)) ,
  (intArray.full ( &( "count" ) ) 100 (replace_Znth (value) (((Znth value positions (0 : Int)) + (Znth (value - 1) positions (0 : Int)))) (positions)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "value" ) )) # Int |-> (value))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
|--
  “ ((value + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (value + 1)) ”

noncomputable def sort_safety_wit_14 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (value : Int) (positions : (List Int)) (output_mixed : (List (Option Int))) (PreH1 : (value >= 100)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed)) = 100)) (PreH6 : ((Zlength (positions)) = 100)) (PreH7 : (1 <= value)) (PreH8 : (value <= 100)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions)) (PreH12 : (Forall ((GE.ge (α := Int)) (n_pre)) positions)) (PreH13 : ((value < 100) -> (((Znth value positions (0 : Int)) + (Znth (value - 1) positions (0 : Int))) <= n_pre))) (PreH14 : (Forall (Eq (None)) output_mixed)) (PreH15 : (CountingCumulativeState input positions value)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
  ** (intArray.full ( &( "count" ) ) 100 positions)
|--
  “ ((n_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre - 1)) ”

noncomputable def sort_safety_wit_15 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (value : Int) (positions : (List Int)) (output_mixed : (List (Option Int))) (PreH1 : (value >= 100)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed)) = 100)) (PreH6 : ((Zlength (positions)) = 100)) (PreH7 : (1 <= value)) (PreH8 : (value <= 100)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions)) (PreH12 : (Forall ((GE.ge (α := Int)) (n_pre)) positions)) (PreH13 : ((value < 100) -> (((Znth value positions (0 : Int)) + (Znth (value - 1) positions (0 : Int))) <= n_pre))) (PreH14 : (Forall (Eq (None)) output_mixed)) (PreH15 : (CountingCumulativeState input positions value)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
  ** (intArray.full ( &( "count" ) ) 100 positions)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def sort_safety_wit_16 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (i : Int) (output_mixed : (List (Option Int))) (bucket_ends : (List Int)) (positions : (List Int)) (sorted : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (sorted)) = n_pre)) (PreH5 : ((Zlength (positions)) = 100)) (PreH6 : ((Zlength (bucket_ends)) = 100)) (PreH7 : ((Zlength (output_mixed)) = 100)) (PreH8 : ((-1) <= i)) (PreH9 : (i < n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH11 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) sorted)) (PreH13 : (Forall ((GT.gt (α := Int)) (100)) sorted)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions)) (PreH15 : (Forall ((GE.ge (α := Int)) (n_pre)) positions)) (PreH16 : ((i >= (0 : Int)) -> (1 <= (Znth (Znth i input (0 : Int)) positions (0 : Int))))) (PreH17 : (Forall (Eq (None)) (sublist (n_pre) (100) (output_mixed)))) (PreH18 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted i)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
  ** (intArray.full ( &( "count" ) ) 100 positions)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def sort_safety_wit_17 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (i : Int) (output_mixed : (List (Option Int))) (bucket_ends : (List Int)) (sorted : (List Int)) (positions : (List Int)) (PreH1 : ((0 : Int) <= (Znth (i) (input) ((0 : Int))))) (PreH2 : ((Znth (i) (input) ((0 : Int))) < 100)) (PreH3 : (1 <= (Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))))) (PreH4 : ((Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))) <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i >= (0 : Int))) (PreH8 : ((0 : Int) <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((Zlength (input)) = n_pre)) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : ((Zlength (positions)) = 100)) (PreH13 : ((Zlength (bucket_ends)) = 100)) (PreH14 : ((Zlength (output_mixed)) = 100)) (PreH15 : ((-1) <= i)) (PreH16 : (i < n_pre)) (PreH17 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH18 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH19 : (Forall ((LE.le (α := Int)) ((0 : Int))) sorted)) (PreH20 : (Forall ((GT.gt (α := Int)) (100)) sorted)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions)) (PreH22 : (Forall ((GE.ge (α := Int)) (n_pre)) positions)) (PreH23 : ((i >= (0 : Int)) -> (1 <= (Znth (Znth i input (0 : Int)) positions (0 : Int))))) (PreH24 : (Forall (Eq (None)) (sublist (n_pre) (100) (output_mixed)))) (PreH25 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted i)) ,
  (intArray.full ( &( "count" ) ) 100 positions)
  ** ((( &( "value" ) )) # Int |-> ((Znth (i) (input) ((0 : Int)))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
|--
  “ (((Znth (Znth (i) (input) ((0 : Int))) positions (0 : Int)) - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth (Znth (i) (input) ((0 : Int))) positions (0 : Int)) - 1)) ”

noncomputable def sort_safety_wit_18 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (i : Int) (output_mixed : (List (Option Int))) (bucket_ends : (List Int)) (sorted : (List Int)) (positions : (List Int)) (PreH1 : ((0 : Int) <= (Znth ((Znth (i) (input) ((0 : Int)))) ((replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))) - 1)) (positions))) ((0 : Int))))) (PreH2 : ((Znth ((Znth (i) (input) ((0 : Int)))) ((replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))) - 1)) (positions))) ((0 : Int))) < 100)) (PreH3 : (i <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : ((0 : Int) <= (Znth (i) (input) ((0 : Int))))) (PreH6 : ((Znth (i) (input) ((0 : Int))) < 100)) (PreH7 : (1 <= (Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))))) (PreH8 : ((Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))) <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i >= (0 : Int))) (PreH12 : ((0 : Int) <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (sorted)) = n_pre)) (PreH16 : ((Zlength (positions)) = 100)) (PreH17 : ((Zlength (bucket_ends)) = 100)) (PreH18 : ((Zlength (output_mixed)) = 100)) (PreH19 : ((-1) <= i)) (PreH20 : (i < n_pre)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH22 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH23 : (Forall ((LE.le (α := Int)) ((0 : Int))) sorted)) (PreH24 : (Forall ((GT.gt (α := Int)) (100)) sorted)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions)) (PreH26 : (Forall ((GE.ge (α := Int)) (n_pre)) positions)) (PreH27 : ((i >= (0 : Int)) -> (1 <= (Znth (Znth i input (0 : Int)) positions (0 : Int))))) (PreH28 : (Forall (Eq (None)) (sublist (n_pre) (100) (output_mixed)))) (PreH29 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted i)) ,
  (intArray.mixed_full ( &( "output" ) ) 100 (replace_Znth ((Znth (Znth (i) (input) ((0 : Int))) (replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth (Znth (i) (input) ((0 : Int))) positions (0 : Int)) - 1)) (positions)) (0 : Int))) ((Some ((Znth (i) (input) ((0 : Int)))))) (output_mixed)))
  ** (intArray.full ( &( "count" ) ) 100 (replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth (Znth (i) (input) ((0 : Int))) positions (0 : Int)) - 1)) (positions)))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def sort_safety_wit_19 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (i : Int) (output_mixed : (List (Option Int))) (bucket_ends : (List Int)) (positions : (List Int)) (sorted : (List Int)) (PreH1 : (i < (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : ((Zlength (positions)) = 100)) (PreH7 : ((Zlength (bucket_ends)) = 100)) (PreH8 : ((Zlength (output_mixed)) = 100)) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH12 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) sorted)) (PreH14 : (Forall ((GT.gt (α := Int)) (100)) sorted)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions)) (PreH16 : (Forall ((GE.ge (α := Int)) (n_pre)) positions)) (PreH17 : ((i >= (0 : Int)) -> (1 <= (Znth (Znth i input (0 : Int)) positions (0 : Int))))) (PreH18 : (Forall (Eq (None)) (sublist (n_pre) (100) (output_mixed)))) (PreH19 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted i)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
  ** (intArray.full ( &( "count" ) ) 100 positions)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def sort_safety_wit_20 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (i : Int) (bucket_starts : (List Int)) (live : (List Int)) (sorted : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : ((Zlength (live)) = n_pre)) (PreH7 : ((Zlength (bucket_starts)) = 100)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) sorted)) (PreH11 : (Forall ((GT.gt (α := Int)) (100)) sorted)) (PreH12 : (CountingSorted input sorted)) (PreH13 : (CountingCopyProgress input sorted live i)) ,
  (intArray.full a_pre n_pre (replace_Znth (i) ((Znth (i - (0 : Int)) sorted (0 : Int))) (live)))
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre sorted)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 100)
  ** (intArray.full ( &( "count" ) ) 100 bucket_starts)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def sort_entail_wit_1 : Prop :=
  (
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH5 : (Forall ((GT.gt (α := Int)) (100)) input)) ,
  (intArray.undef_full ( &( "output" ) ) 100)
  ** (intArray.undef_full ( &( "count" ) ) 100)
  ** (intArray.full a_pre n_pre input)
|--
  EX count_mixed : (List (Option Int)), EX output_mixed : (List (Option Int)),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (output_mixed)) = 100) ” &&
  “ ((Zlength (count_mixed)) = 100) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 100) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) input) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) input) ” &&
  “ (Forall (Eq (None)) output_mixed) ” &&
  “ (CountingZeroedPrefix count_mixed (0 : Int)) ”
  &&  (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
  ** (intArray.mixed_full ( &( "count" ) ) 100 count_mixed)
) \/
(
forall (input : (List Int)) (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH5 : (Forall ((GT.gt (α := Int)) (100)) input)) ,
  (intArray.undef_full ( &( "output" ) ) 100)
  ** (intArray.undef_full ( &( "count" ) ) 100)
|--
  EX count_mixed : (List (Option Int)), EX output_mixed : (List (Option Int)),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (output_mixed)) = 100) ” &&
  “ ((Zlength (count_mixed)) = 100) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 100) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) input) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) input) ” &&
  “ (Forall (Eq (None)) output_mixed) ” &&
  “ (CountingZeroedPrefix count_mixed (0 : Int)) ”
  &&  (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
  ** (intArray.mixed_full ( &( "count" ) ) 100 count_mixed)
)

noncomputable def sort_entail_wit_2 : Prop :=
  (
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (value : Int) (count_mixed_2 : (List (Option Int))) (output_mixed_2 : (List (Option Int))) (PreH1 : (value < 100)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (count_mixed_2)) = 100)) (PreH7 : ((0 : Int) <= value)) (PreH8 : (value <= 100)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall (Eq (None)) output_mixed_2)) (PreH12 : (CountingZeroedPrefix count_mixed_2 value)) ,
  (intArray.mixed_full ( &( "count" ) ) 100 (replace_Znth (value) ((Some ((0 : Int)))) (count_mixed_2)))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed_2)
|--
  EX count_mixed : (List (Option Int)), EX output_mixed : (List (Option Int)),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (output_mixed)) = 100) ” &&
  “ ((Zlength (count_mixed)) = 100) ” &&
  “ ((0 : Int) <= (value + 1)) ” &&
  “ ((value + 1) <= 100) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) input) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) input) ” &&
  “ (Forall (Eq (None)) output_mixed) ” &&
  “ (CountingZeroedPrefix count_mixed (value + 1)) ”
  &&  (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
  ** (intArray.mixed_full ( &( "count" ) ) 100 count_mixed)
) \/
(
forall (input : (List Int)) (n_pre : Int) (value : Int) (count_mixed_2 : (List (Option Int))) (output_mixed_2 : (List (Option Int))) (PreH1 : (value < 100)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (count_mixed_2)) = 100)) (PreH7 : ((0 : Int) <= value)) (PreH8 : (value <= 100)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall (Eq (None)) output_mixed_2)) (PreH12 : (CountingZeroedPrefix count_mixed_2 value)) ,
  TT && emp 
|--
  “ (CountingZeroedPrefix (replace_Znth (value) ((Some ((0 : Int)))) (count_mixed_2)) (value + 1)) ” &&
  “ ((Zlength ((replace_Znth (value) ((Some ((0 : Int)))) (count_mixed_2)))) = 100) ”
  &&  emp
)

noncomputable def sort_entail_wit_2_split_goal_1 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (value : Int) (count_mixed_2 : (List (Option Int))) (output_mixed_2 : (List (Option Int))) (PreH1 : (value < 100)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (count_mixed_2)) = 100)) (PreH7 : ((0 : Int) <= value)) (PreH8 : (value <= 100)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall (Eq (None)) output_mixed_2)) (PreH12 : (CountingZeroedPrefix count_mixed_2 value)) ,
  (CountingZeroedPrefix (replace_Znth (value) ((Some ((0 : Int)))) (count_mixed_2)) (value + 1))

noncomputable def sort_entail_wit_2_split_goal_2 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (value : Int) (count_mixed_2 : (List (Option Int))) (output_mixed_2 : (List (Option Int))) (PreH1 : (value < 100)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (count_mixed_2)) = 100)) (PreH7 : ((0 : Int) <= value)) (PreH8 : (value <= 100)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall (Eq (None)) output_mixed_2)) (PreH12 : (CountingZeroedPrefix count_mixed_2 value)) ,
  ((Zlength ((replace_Znth (value) ((Some ((0 : Int)))) (count_mixed_2)))) = 100)

noncomputable def sort_entail_wit_3 : Prop :=
  (
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (value : Int) (count_mixed : (List (Option Int))) (output_mixed_2 : (List (Option Int))) (PreH1 : (value >= 100)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (count_mixed)) = 100)) (PreH7 : ((0 : Int) <= value)) (PreH8 : (value <= 100)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall (Eq (None)) output_mixed_2)) (PreH12 : (CountingZeroedPrefix count_mixed value)) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed_2)
  ** (intArray.mixed_full ( &( "count" ) ) 100 count_mixed)
|--
  EX counts : (List Int), EX output_mixed : (List (Option Int)),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (output_mixed)) = 100) ” &&
  “ ((Zlength (counts)) = 100) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) input) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) input) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts) ” &&
  “ (Forall ((GE.ge (α := Int)) ((0 : Int))) counts) ” &&
  “ (Forall (Eq (None)) output_mixed) ” &&
  “ (CountingHistogramPrefix input counts (0 : Int)) ”
  &&  (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
  ** (intArray.full ( &( "count" ) ) 100 counts)
) \/
(
forall (input : (List Int)) (n_pre : Int) (value : Int) (count_mixed : (List (Option Int))) (output_mixed_2 : (List (Option Int))) (PreH1 : (value >= 100)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (count_mixed)) = 100)) (PreH7 : ((0 : Int) <= value)) (PreH8 : (value <= 100)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall (Eq (None)) output_mixed_2)) (PreH12 : (CountingZeroedPrefix count_mixed value)) ,
  (intArray.mixed_full ( &( "count" ) ) 100 count_mixed)
|--
  EX counts : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (output_mixed_2)) = 100) ” &&
  “ ((Zlength (counts)) = 100) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) input) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) input) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts) ” &&
  “ (Forall ((GE.ge (α := Int)) ((0 : Int))) counts) ” &&
  “ (Forall (Eq (None)) output_mixed_2) ” &&
  “ (CountingHistogramPrefix input counts (0 : Int)) ”
  &&  (intArray.full ( &( "count" ) ) 100 counts)
)

noncomputable def sort_entail_wit_4 : Prop :=
  (
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (i : Int) (output_mixed : (List (Option Int))) (counts : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed)) = 100)) (PreH6 : ((Zlength (counts)) = 100)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts)) (PreH12 : (Forall ((GE.ge (α := Int)) (i)) counts)) (PreH13 : (Forall (Eq (None)) output_mixed)) (PreH14 : (CountingHistogramPrefix input counts i)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
  ** (intArray.full ( &( "count" ) ) 100 counts)
|--
  “ ((0 : Int) <= (Znth i input (0 : Int))) ” &&
  “ ((Znth i input (0 : Int)) < 100) ” &&
  “ ((0 : Int) <= (Znth (Znth i input (0 : Int)) counts (0 : Int))) ” &&
  “ ((Znth (Znth i input (0 : Int)) counts (0 : Int)) < 100) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (output_mixed)) = 100) ” &&
  “ ((Zlength (counts)) = 100) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) input) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) input) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts) ” &&
  “ (Forall ((GE.ge (α := Int)) (i)) counts) ” &&
  “ (Forall (Eq (None)) output_mixed) ” &&
  “ (CountingHistogramPrefix input counts i) ”
  &&  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
  ** (intArray.full ( &( "count" ) ) 100 counts)
) \/
(
forall (input : (List Int)) (n_pre : Int) (i : Int) (output_mixed : (List (Option Int))) (counts : (List Int)) (PreH1 : (i <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (i >= INT_MIN)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (i < n_pre)) (PreH6 : ((0 : Int) <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : ((Zlength (output_mixed)) = 100)) (PreH10 : ((Zlength (counts)) = 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH14 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts)) (PreH16 : (Forall ((GE.ge (α := Int)) (i)) counts)) (PreH17 : (Forall (Eq (None)) output_mixed)) (PreH18 : (CountingHistogramPrefix input counts i)) ,
  TT && emp 
|--
  “ ((Znth (Znth i input (0 : Int)) counts (0 : Int)) < 100) ” &&
  “ ((0 : Int) <= (Znth (Znth i input (0 : Int)) counts (0 : Int))) ” &&
  “ ((Znth i input (0 : Int)) < 100) ” &&
  “ ((0 : Int) <= (Znth i input (0 : Int))) ”
  &&  emp
)

noncomputable def sort_entail_wit_4_split_goal_1 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (i : Int) (output_mixed : (List (Option Int))) (counts : (List Int)) (PreH1 : (i <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (i >= INT_MIN)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (i < n_pre)) (PreH6 : ((0 : Int) <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : ((Zlength (output_mixed)) = 100)) (PreH10 : ((Zlength (counts)) = 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH14 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts)) (PreH16 : (Forall ((GE.ge (α := Int)) (i)) counts)) (PreH17 : (Forall (Eq (None)) output_mixed)) (PreH18 : (CountingHistogramPrefix input counts i)) ,
  ((Znth (Znth i input (0 : Int)) counts (0 : Int)) < 100)

noncomputable def sort_entail_wit_4_split_goal_2 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (i : Int) (output_mixed : (List (Option Int))) (counts : (List Int)) (PreH1 : (i <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (i >= INT_MIN)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (i < n_pre)) (PreH6 : ((0 : Int) <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : ((Zlength (output_mixed)) = 100)) (PreH10 : ((Zlength (counts)) = 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH14 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts)) (PreH16 : (Forall ((GE.ge (α := Int)) (i)) counts)) (PreH17 : (Forall (Eq (None)) output_mixed)) (PreH18 : (CountingHistogramPrefix input counts i)) ,
  ((0 : Int) <= (Znth (Znth i input (0 : Int)) counts (0 : Int)))

noncomputable def sort_entail_wit_4_split_goal_3 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (i : Int) (output_mixed : (List (Option Int))) (counts : (List Int)) (PreH1 : (i <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (i >= INT_MIN)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (i < n_pre)) (PreH6 : ((0 : Int) <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : ((Zlength (output_mixed)) = 100)) (PreH10 : ((Zlength (counts)) = 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH14 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts)) (PreH16 : (Forall ((GE.ge (α := Int)) (i)) counts)) (PreH17 : (Forall (Eq (None)) output_mixed)) (PreH18 : (CountingHistogramPrefix input counts i)) ,
  ((Znth i input (0 : Int)) < 100)

noncomputable def sort_entail_wit_4_split_goal_4 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (i : Int) (output_mixed : (List (Option Int))) (counts : (List Int)) (PreH1 : (i <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (i >= INT_MIN)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (i < n_pre)) (PreH6 : ((0 : Int) <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : ((Zlength (output_mixed)) = 100)) (PreH10 : ((Zlength (counts)) = 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH14 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts)) (PreH16 : (Forall ((GE.ge (α := Int)) (i)) counts)) (PreH17 : (Forall (Eq (None)) output_mixed)) (PreH18 : (CountingHistogramPrefix input counts i)) ,
  ((0 : Int) <= (Znth i input (0 : Int)))

noncomputable def sort_entail_wit_5 : Prop :=
  (
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (i : Int) (output_mixed_2 : (List (Option Int))) (counts_2 : (List Int)) (PreH1 : ((0 : Int) <= (Znth i input (0 : Int)))) (PreH2 : ((Znth i input (0 : Int)) < 100)) (PreH3 : ((0 : Int) <= (Znth (Znth i input (0 : Int)) counts_2 (0 : Int)))) (PreH4 : ((Znth (Znth i input (0 : Int)) counts_2 (0 : Int)) < 100)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((Zlength (input)) = n_pre)) (PreH11 : ((Zlength (output_mixed_2)) = 100)) (PreH12 : ((Zlength (counts_2)) = 100)) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH16 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH17 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_2)) (PreH18 : (Forall ((GE.ge (α := Int)) (i)) counts_2)) (PreH19 : (Forall (Eq (None)) output_mixed_2)) (PreH20 : (CountingHistogramPrefix input counts_2 i)) ,
  (intArray.full ( &( "count" ) ) 100 (replace_Znth ((Znth i input (0 : Int))) (((Znth (Znth i input (0 : Int)) counts_2 (0 : Int)) + 1)) (counts_2)))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed_2)
|--
  EX counts : (List Int), EX output_mixed : (List (Option Int)),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (output_mixed)) = 100) ” &&
  “ ((Zlength (counts)) = 100) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) input) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) input) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts) ” &&
  “ (Forall ((GE.ge (α := Int)) ((i + 1))) counts) ” &&
  “ (Forall (Eq (None)) output_mixed) ” &&
  “ (CountingHistogramPrefix input counts (i + 1)) ”
  &&  (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
  ** (intArray.full ( &( "count" ) ) 100 counts)
) \/
(
forall (input : (List Int)) (n_pre : Int) (i : Int) (output_mixed_2 : (List (Option Int))) (counts_2 : (List Int)) (PreH1 : ((0 : Int) <= (Znth i input (0 : Int)))) (PreH2 : ((Znth i input (0 : Int)) < 100)) (PreH3 : ((0 : Int) <= (Znth (Znth i input (0 : Int)) counts_2 (0 : Int)))) (PreH4 : ((Znth (Znth i input (0 : Int)) counts_2 (0 : Int)) < 100)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((Zlength (input)) = n_pre)) (PreH11 : ((Zlength (output_mixed_2)) = 100)) (PreH12 : ((Zlength (counts_2)) = 100)) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH16 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH17 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_2)) (PreH18 : (Forall ((GE.ge (α := Int)) (i)) counts_2)) (PreH19 : (Forall (Eq (None)) output_mixed_2)) (PreH20 : (CountingHistogramPrefix input counts_2 i)) ,
  TT && emp 
|--
  “ (CountingHistogramPrefix input (replace_Znth ((Znth i input (0 : Int))) (((Znth (Znth i input (0 : Int)) counts_2 (0 : Int)) + 1)) (counts_2)) (i + 1)) ” &&
  “ (Forall ((GE.ge (α := Int)) ((i + 1))) (replace_Znth ((Znth i input (0 : Int))) (((Znth (Znth i input (0 : Int)) counts_2 (0 : Int)) + 1)) (counts_2))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (replace_Znth ((Znth i input (0 : Int))) (((Znth (Znth i input (0 : Int)) counts_2 (0 : Int)) + 1)) (counts_2))) ” &&
  “ ((Zlength ((replace_Znth ((Znth i input (0 : Int))) (((Znth (Znth i input (0 : Int)) counts_2 (0 : Int)) + 1)) (counts_2)))) = 100) ”
  &&  emp
)

noncomputable def sort_entail_wit_5_split_goal_1 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (i : Int) (output_mixed_2 : (List (Option Int))) (counts_2 : (List Int)) (PreH1 : ((0 : Int) <= (Znth i input (0 : Int)))) (PreH2 : ((Znth i input (0 : Int)) < 100)) (PreH3 : ((0 : Int) <= (Znth (Znth i input (0 : Int)) counts_2 (0 : Int)))) (PreH4 : ((Znth (Znth i input (0 : Int)) counts_2 (0 : Int)) < 100)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((Zlength (input)) = n_pre)) (PreH11 : ((Zlength (output_mixed_2)) = 100)) (PreH12 : ((Zlength (counts_2)) = 100)) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH16 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH17 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_2)) (PreH18 : (Forall ((GE.ge (α := Int)) (i)) counts_2)) (PreH19 : (Forall (Eq (None)) output_mixed_2)) (PreH20 : (CountingHistogramPrefix input counts_2 i)) ,
  (CountingHistogramPrefix input (replace_Znth ((Znth i input (0 : Int))) (((Znth (Znth i input (0 : Int)) counts_2 (0 : Int)) + 1)) (counts_2)) (i + 1))

noncomputable def sort_entail_wit_5_split_goal_2 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (i : Int) (output_mixed_2 : (List (Option Int))) (counts_2 : (List Int)) (PreH1 : ((0 : Int) <= (Znth i input (0 : Int)))) (PreH2 : ((Znth i input (0 : Int)) < 100)) (PreH3 : ((0 : Int) <= (Znth (Znth i input (0 : Int)) counts_2 (0 : Int)))) (PreH4 : ((Znth (Znth i input (0 : Int)) counts_2 (0 : Int)) < 100)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((Zlength (input)) = n_pre)) (PreH11 : ((Zlength (output_mixed_2)) = 100)) (PreH12 : ((Zlength (counts_2)) = 100)) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH16 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH17 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_2)) (PreH18 : (Forall ((GE.ge (α := Int)) (i)) counts_2)) (PreH19 : (Forall (Eq (None)) output_mixed_2)) (PreH20 : (CountingHistogramPrefix input counts_2 i)) ,
  (Forall ((GE.ge (α := Int)) ((i + 1))) (replace_Znth ((Znth i input (0 : Int))) (((Znth (Znth i input (0 : Int)) counts_2 (0 : Int)) + 1)) (counts_2)))

noncomputable def sort_entail_wit_5_split_goal_3 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (i : Int) (output_mixed_2 : (List (Option Int))) (counts_2 : (List Int)) (PreH1 : ((0 : Int) <= (Znth i input (0 : Int)))) (PreH2 : ((Znth i input (0 : Int)) < 100)) (PreH3 : ((0 : Int) <= (Znth (Znth i input (0 : Int)) counts_2 (0 : Int)))) (PreH4 : ((Znth (Znth i input (0 : Int)) counts_2 (0 : Int)) < 100)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((Zlength (input)) = n_pre)) (PreH11 : ((Zlength (output_mixed_2)) = 100)) (PreH12 : ((Zlength (counts_2)) = 100)) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH16 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH17 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_2)) (PreH18 : (Forall ((GE.ge (α := Int)) (i)) counts_2)) (PreH19 : (Forall (Eq (None)) output_mixed_2)) (PreH20 : (CountingHistogramPrefix input counts_2 i)) ,
  (Forall ((LE.le (α := Int)) ((0 : Int))) (replace_Znth ((Znth i input (0 : Int))) (((Znth (Znth i input (0 : Int)) counts_2 (0 : Int)) + 1)) (counts_2)))

noncomputable def sort_entail_wit_5_split_goal_4 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (i : Int) (output_mixed_2 : (List (Option Int))) (counts_2 : (List Int)) (PreH1 : ((0 : Int) <= (Znth i input (0 : Int)))) (PreH2 : ((Znth i input (0 : Int)) < 100)) (PreH3 : ((0 : Int) <= (Znth (Znth i input (0 : Int)) counts_2 (0 : Int)))) (PreH4 : ((Znth (Znth i input (0 : Int)) counts_2 (0 : Int)) < 100)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((Zlength (input)) = n_pre)) (PreH11 : ((Zlength (output_mixed_2)) = 100)) (PreH12 : ((Zlength (counts_2)) = 100)) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH16 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH17 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_2)) (PreH18 : (Forall ((GE.ge (α := Int)) (i)) counts_2)) (PreH19 : (Forall (Eq (None)) output_mixed_2)) (PreH20 : (CountingHistogramPrefix input counts_2 i)) ,
  ((Zlength ((replace_Znth ((Znth i input (0 : Int))) (((Znth (Znth i input (0 : Int)) counts_2 (0 : Int)) + 1)) (counts_2)))) = 100)

noncomputable def sort_entail_wit_6 : Prop :=
  (
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (i : Int) (counts : (List Int)) (output_mixed_2 : (List (Option Int))) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (counts)) = 100)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts)) (PreH12 : (Forall ((GE.ge (α := Int)) (i)) counts)) (PreH13 : (Forall (Eq (None)) output_mixed_2)) (PreH14 : (CountingHistogramPrefix input counts i)) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed_2)
  ** (intArray.full ( &( "count" ) ) 100 counts)
|--
  EX positions : (List Int), EX output_mixed : (List (Option Int)),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (output_mixed)) = 100) ” &&
  “ ((Zlength (positions)) = 100) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= 100) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) input) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) input) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) positions) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) positions) ” &&
  “ ((1 < 100) -> (((Znth 1 positions (0 : Int)) + (Znth (1 - 1) positions (0 : Int))) <= n_pre)) ” &&
  “ (Forall (Eq (None)) output_mixed) ” &&
  “ (CountingCumulativeState input positions 1) ”
  &&  (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
  ** (intArray.full ( &( "count" ) ) 100 positions)
) \/
(
forall (input : (List Int)) (n_pre : Int) (i : Int) (counts : (List Int)) (output_mixed_2 : (List (Option Int))) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (counts)) = 100)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts)) (PreH12 : (Forall ((GE.ge (α := Int)) (i)) counts)) (PreH13 : (Forall (Eq (None)) output_mixed_2)) (PreH14 : (CountingHistogramPrefix input counts i)) ,
  TT && emp 
|--
  “ (CountingCumulativeState input counts 1) ” &&
  “ ((1 < 100) -> (((Znth 1 counts (0 : Int)) + (Znth (1 - 1) counts (0 : Int))) <= n_pre)) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) counts) ”
  &&  emp
)

noncomputable def sort_entail_wit_6_split_goal_1 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (i : Int) (counts : (List Int)) (output_mixed_2 : (List (Option Int))) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (counts)) = 100)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts)) (PreH12 : (Forall ((GE.ge (α := Int)) (i)) counts)) (PreH13 : (Forall (Eq (None)) output_mixed_2)) (PreH14 : (CountingHistogramPrefix input counts i)) ,
  (CountingCumulativeState input counts 1)

noncomputable def sort_entail_wit_6_split_goal_2 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (i : Int) (counts : (List Int)) (output_mixed_2 : (List (Option Int))) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (counts)) = 100)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts)) (PreH12 : (Forall ((GE.ge (α := Int)) (i)) counts)) (PreH13 : (Forall (Eq (None)) output_mixed_2)) (PreH14 : (CountingHistogramPrefix input counts i)) ,
  ((1 < 100) -> (((Znth 1 counts (0 : Int)) + (Znth (1 - 1) counts (0 : Int))) <= n_pre))

noncomputable def sort_entail_wit_6_split_goal_3 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (i : Int) (counts : (List Int)) (output_mixed_2 : (List (Option Int))) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (counts)) = 100)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts)) (PreH12 : (Forall ((GE.ge (α := Int)) (i)) counts)) (PreH13 : (Forall (Eq (None)) output_mixed_2)) (PreH14 : (CountingHistogramPrefix input counts i)) ,
  (Forall ((GE.ge (α := Int)) (n_pre)) counts)

noncomputable def sort_entail_wit_7 : Prop :=
  (
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (value : Int) (positions_2 : (List Int)) (output_mixed_2 : (List (Option Int))) (PreH1 : (value < 100)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (positions_2)) = 100)) (PreH7 : (1 <= value)) (PreH8 : (value <= 100)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions_2)) (PreH12 : (Forall ((GE.ge (α := Int)) (n_pre)) positions_2)) (PreH13 : ((value < 100) -> (((Znth value positions_2 (0 : Int)) + (Znth (value - 1) positions_2 (0 : Int))) <= n_pre))) (PreH14 : (Forall (Eq (None)) output_mixed_2)) (PreH15 : (CountingCumulativeState input positions_2 value)) ,
  (intArray.full ( &( "count" ) ) 100 (replace_Znth (value) (((Znth value positions_2 (0 : Int)) + (Znth (value - 1) positions_2 (0 : Int)))) (positions_2)))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed_2)
|--
  EX positions : (List Int), EX output_mixed : (List (Option Int)),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (output_mixed)) = 100) ” &&
  “ ((Zlength (positions)) = 100) ” &&
  “ (1 <= (value + 1)) ” &&
  “ ((value + 1) <= 100) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) input) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) input) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) positions) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) positions) ” &&
  “ (((value + 1) < 100) -> (((Znth (value + 1) positions (0 : Int)) + (Znth ((value + 1) - 1) positions (0 : Int))) <= n_pre)) ” &&
  “ (Forall (Eq (None)) output_mixed) ” &&
  “ (CountingCumulativeState input positions (value + 1)) ”
  &&  (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
  ** (intArray.full ( &( "count" ) ) 100 positions)
) \/
(
forall (input : (List Int)) (n_pre : Int) (value : Int) (positions_2 : (List Int)) (output_mixed_2 : (List (Option Int))) (PreH1 : (value < 100)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (positions_2)) = 100)) (PreH7 : (1 <= value)) (PreH8 : (value <= 100)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions_2)) (PreH12 : (Forall ((GE.ge (α := Int)) (n_pre)) positions_2)) (PreH13 : ((value < 100) -> (((Znth value positions_2 (0 : Int)) + (Znth (value - 1) positions_2 (0 : Int))) <= n_pre))) (PreH14 : (Forall (Eq (None)) output_mixed_2)) (PreH15 : (CountingCumulativeState input positions_2 value)) ,
  TT && emp 
|--
  “ (CountingCumulativeState input (replace_Znth (value) (((Znth value positions_2 (0 : Int)) + (Znth (value - 1) positions_2 (0 : Int)))) (positions_2)) (value + 1)) ” &&
  “ (((value + 1) < 100) -> (((Znth (value + 1) (replace_Znth (value) (((Znth value positions_2 (0 : Int)) + (Znth (value - 1) positions_2 (0 : Int)))) (positions_2)) (0 : Int)) + (Znth ((value + 1) - 1) (replace_Znth (value) (((Znth value positions_2 (0 : Int)) + (Znth (value - 1) positions_2 (0 : Int)))) (positions_2)) (0 : Int))) <= n_pre)) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) (replace_Znth (value) (((Znth value positions_2 (0 : Int)) + (Znth (value - 1) positions_2 (0 : Int)))) (positions_2))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (replace_Znth (value) (((Znth value positions_2 (0 : Int)) + (Znth (value - 1) positions_2 (0 : Int)))) (positions_2))) ” &&
  “ ((Zlength ((replace_Znth (value) (((Znth value positions_2 (0 : Int)) + (Znth (value - 1) positions_2 (0 : Int)))) (positions_2)))) = 100) ”
  &&  emp
)

noncomputable def sort_entail_wit_7_split_goal_1 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (value : Int) (positions_2 : (List Int)) (output_mixed_2 : (List (Option Int))) (PreH1 : (value < 100)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (positions_2)) = 100)) (PreH7 : (1 <= value)) (PreH8 : (value <= 100)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions_2)) (PreH12 : (Forall ((GE.ge (α := Int)) (n_pre)) positions_2)) (PreH13 : ((value < 100) -> (((Znth value positions_2 (0 : Int)) + (Znth (value - 1) positions_2 (0 : Int))) <= n_pre))) (PreH14 : (Forall (Eq (None)) output_mixed_2)) (PreH15 : (CountingCumulativeState input positions_2 value)) ,
  (CountingCumulativeState input (replace_Znth (value) (((Znth value positions_2 (0 : Int)) + (Znth (value - 1) positions_2 (0 : Int)))) (positions_2)) (value + 1))

noncomputable def sort_entail_wit_7_split_goal_2 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (value : Int) (positions_2 : (List Int)) (output_mixed_2 : (List (Option Int))) (PreH1 : (value < 100)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (positions_2)) = 100)) (PreH7 : (1 <= value)) (PreH8 : (value <= 100)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions_2)) (PreH12 : (Forall ((GE.ge (α := Int)) (n_pre)) positions_2)) (PreH13 : ((value < 100) -> (((Znth value positions_2 (0 : Int)) + (Znth (value - 1) positions_2 (0 : Int))) <= n_pre))) (PreH14 : (Forall (Eq (None)) output_mixed_2)) (PreH15 : (CountingCumulativeState input positions_2 value)) ,
  (((value + 1) < 100) -> (((Znth (value + 1) (replace_Znth (value) (((Znth value positions_2 (0 : Int)) + (Znth (value - 1) positions_2 (0 : Int)))) (positions_2)) (0 : Int)) + (Znth ((value + 1) - 1) (replace_Znth (value) (((Znth value positions_2 (0 : Int)) + (Znth (value - 1) positions_2 (0 : Int)))) (positions_2)) (0 : Int))) <= n_pre))

noncomputable def sort_entail_wit_7_split_goal_3 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (value : Int) (positions_2 : (List Int)) (output_mixed_2 : (List (Option Int))) (PreH1 : (value < 100)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (positions_2)) = 100)) (PreH7 : (1 <= value)) (PreH8 : (value <= 100)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions_2)) (PreH12 : (Forall ((GE.ge (α := Int)) (n_pre)) positions_2)) (PreH13 : ((value < 100) -> (((Znth value positions_2 (0 : Int)) + (Znth (value - 1) positions_2 (0 : Int))) <= n_pre))) (PreH14 : (Forall (Eq (None)) output_mixed_2)) (PreH15 : (CountingCumulativeState input positions_2 value)) ,
  (Forall ((GE.ge (α := Int)) (n_pre)) (replace_Znth (value) (((Znth value positions_2 (0 : Int)) + (Znth (value - 1) positions_2 (0 : Int)))) (positions_2)))

noncomputable def sort_entail_wit_7_split_goal_4 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (value : Int) (positions_2 : (List Int)) (output_mixed_2 : (List (Option Int))) (PreH1 : (value < 100)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (positions_2)) = 100)) (PreH7 : (1 <= value)) (PreH8 : (value <= 100)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions_2)) (PreH12 : (Forall ((GE.ge (α := Int)) (n_pre)) positions_2)) (PreH13 : ((value < 100) -> (((Znth value positions_2 (0 : Int)) + (Znth (value - 1) positions_2 (0 : Int))) <= n_pre))) (PreH14 : (Forall (Eq (None)) output_mixed_2)) (PreH15 : (CountingCumulativeState input positions_2 value)) ,
  (Forall ((LE.le (α := Int)) ((0 : Int))) (replace_Znth (value) (((Znth value positions_2 (0 : Int)) + (Znth (value - 1) positions_2 (0 : Int)))) (positions_2)))

noncomputable def sort_entail_wit_7_split_goal_5 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (value : Int) (positions_2 : (List Int)) (output_mixed_2 : (List (Option Int))) (PreH1 : (value < 100)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (positions_2)) = 100)) (PreH7 : (1 <= value)) (PreH8 : (value <= 100)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions_2)) (PreH12 : (Forall ((GE.ge (α := Int)) (n_pre)) positions_2)) (PreH13 : ((value < 100) -> (((Znth value positions_2 (0 : Int)) + (Znth (value - 1) positions_2 (0 : Int))) <= n_pre))) (PreH14 : (Forall (Eq (None)) output_mixed_2)) (PreH15 : (CountingCumulativeState input positions_2 value)) ,
  ((Zlength ((replace_Znth (value) (((Znth value positions_2 (0 : Int)) + (Znth (value - 1) positions_2 (0 : Int)))) (positions_2)))) = 100)

noncomputable def sort_entail_wit_8 : Prop :=
  (
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (value : Int) (positions_2 : (List Int)) (output_mixed_2 : (List (Option Int))) (PreH1 : (value >= 100)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (positions_2)) = 100)) (PreH7 : (1 <= value)) (PreH8 : (value <= 100)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions_2)) (PreH12 : (Forall ((GE.ge (α := Int)) (n_pre)) positions_2)) (PreH13 : ((value < 100) -> (((Znth value positions_2 (0 : Int)) + (Znth (value - 1) positions_2 (0 : Int))) <= n_pre))) (PreH14 : (Forall (Eq (None)) output_mixed_2)) (PreH15 : (CountingCumulativeState input positions_2 value)) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed_2)
  ** (intArray.full ( &( "count" ) ) 100 positions_2)
|--
  EX output_mixed : (List (Option Int)), EX bucket_ends : (List Int), EX positions : (List Int), EX sorted : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (sorted)) = n_pre) ” &&
  “ ((Zlength (positions)) = 100) ” &&
  “ ((Zlength (bucket_ends)) = 100) ” &&
  “ ((Zlength (output_mixed)) = 100) ” &&
  “ ((-1) <= (n_pre - 1)) ” &&
  “ ((n_pre - 1) < n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) input) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) input) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) sorted) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) sorted) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) positions) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) positions) ” &&
  “ (((n_pre - 1) >= (0 : Int)) -> (1 <= (Znth (Znth (n_pre - 1) input (0 : Int)) positions (0 : Int)))) ” &&
  “ (Forall (Eq (None)) (sublist (n_pre) (100) (output_mixed))) ” &&
  “ (CountingPlacementProgress input positions bucket_ends output_mixed sorted (n_pre - 1)) ”
  &&  (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
  ** (intArray.full ( &( "count" ) ) 100 positions)
) \/
(
forall (input : (List Int)) (n_pre : Int) (value : Int) (positions_2 : (List Int)) (output_mixed_2 : (List (Option Int))) (PreH1 : (value >= 100)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed_2)) = 100)) (PreH6 : ((Zlength (positions_2)) = 100)) (PreH7 : (1 <= value)) (PreH8 : (value <= 100)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions_2)) (PreH12 : (Forall ((GE.ge (α := Int)) (n_pre)) positions_2)) (PreH13 : ((value < 100) -> (((Znth value positions_2 (0 : Int)) + (Znth (value - 1) positions_2 (0 : Int))) <= n_pre))) (PreH14 : (Forall (Eq (None)) output_mixed_2)) (PreH15 : (CountingCumulativeState input positions_2 value)) ,
  TT && emp 
|--
  EX bucket_ends : (List Int), EX sorted : (List Int),
  “ ((Zlength (sorted)) = (Zlength (input))) ” &&
  “ ((Zlength (bucket_ends)) = 100) ” &&
  “ ((-1) <= ((Zlength (input)) - 1)) ” &&
  “ (((Zlength (input)) - 1) < (Zlength (input))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) sorted) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) sorted) ” &&
  “ ((((Zlength (input)) - 1) >= (0 : Int)) -> (1 <= (Znth (Znth ((Zlength (input)) - 1) input (0 : Int)) positions_2 (0 : Int)))) ” &&
  “ (Forall (Eq (None)) (sublist ((Zlength (input))) (100) (output_mixed_2))) ” &&
  “ (CountingPlacementProgress input positions_2 bucket_ends output_mixed_2 sorted ((Zlength (input)) - 1)) ”
  &&  emp
)

noncomputable def sort_entail_wit_9 : Prop :=
  (
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (i : Int) (output_mixed : (List (Option Int))) (bucket_ends : (List Int)) (sorted : (List Int)) (positions : (List Int)) (PreH1 : (i >= (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : ((Zlength (positions)) = 100)) (PreH7 : ((Zlength (bucket_ends)) = 100)) (PreH8 : ((Zlength (output_mixed)) = 100)) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH12 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) sorted)) (PreH14 : (Forall ((GT.gt (α := Int)) (100)) sorted)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions)) (PreH16 : (Forall ((GE.ge (α := Int)) (n_pre)) positions)) (PreH17 : ((i >= (0 : Int)) -> (1 <= (Znth (Znth i input (0 : Int)) positions (0 : Int))))) (PreH18 : (Forall (Eq (None)) (sublist (n_pre) (100) (output_mixed)))) (PreH19 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted i)) ,
  (intArray.full a_pre n_pre input)
  ** ((( &( "value" ) )) # Int |-> ((Znth i input (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
  ** (intArray.full ( &( "count" ) ) 100 positions)
|--
  “ ((0 : Int) <= (Znth (i) (input) ((0 : Int)))) ” &&
  “ ((Znth (i) (input) ((0 : Int))) < 100) ” &&
  “ ((Znth (i) (input) ((0 : Int))) = (Znth (i) (input) ((0 : Int)))) ” &&
  “ (1 <= (Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int)))) ” &&
  “ ((Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))) <= n_pre) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (i >= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (sorted)) = n_pre) ” &&
  “ ((Zlength (positions)) = 100) ” &&
  “ ((Zlength (bucket_ends)) = 100) ” &&
  “ ((Zlength (output_mixed)) = 100) ” &&
  “ ((-1) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) input) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) input) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) sorted) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) sorted) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) positions) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) positions) ” &&
  “ ((i >= (0 : Int)) -> (1 <= (Znth (Znth i input (0 : Int)) positions (0 : Int)))) ” &&
  “ (Forall (Eq (None)) (sublist (n_pre) (100) (output_mixed))) ” &&
  “ (CountingPlacementProgress input positions bucket_ends output_mixed sorted i) ”
  &&  ((( &( "value" ) )) # Int |-> ((Znth (i) (input) ((0 : Int)))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
  ** (intArray.full ( &( "count" ) ) 100 positions)
) \/
(
forall (input : (List Int)) (n_pre : Int) (i : Int) (output_mixed : (List (Option Int))) (bucket_ends : (List Int)) (sorted : (List Int)) (positions : (List Int)) (PreH1 : (i <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : ((Znth i input (0 : Int)) <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (n_pre >= INT_MIN)) (PreH6 : ((Znth i input (0 : Int)) >= INT_MIN)) (PreH7 : (i >= (0 : Int))) (PreH8 : ((0 : Int) <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((Zlength (input)) = n_pre)) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : ((Zlength (positions)) = 100)) (PreH13 : ((Zlength (bucket_ends)) = 100)) (PreH14 : ((Zlength (output_mixed)) = 100)) (PreH15 : ((-1) <= i)) (PreH16 : (i < n_pre)) (PreH17 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH18 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH19 : (Forall ((LE.le (α := Int)) ((0 : Int))) sorted)) (PreH20 : (Forall ((GT.gt (α := Int)) (100)) sorted)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions)) (PreH22 : (Forall ((GE.ge (α := Int)) (n_pre)) positions)) (PreH23 : ((i >= (0 : Int)) -> (1 <= (Znth (Znth i input (0 : Int)) positions (0 : Int))))) (PreH24 : (Forall (Eq (None)) (sublist (n_pre) (100) (output_mixed)))) (PreH25 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted i)) ,
  TT && emp 
|--
  “ ((Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))) <= n_pre) ” &&
  “ ((Znth (i) (input) ((0 : Int))) < 100) ” &&
  “ ((0 : Int) <= (Znth (i) (input) ((0 : Int)))) ”
  &&  emp
)

noncomputable def sort_entail_wit_9_split_goal_1 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (i : Int) (output_mixed : (List (Option Int))) (bucket_ends : (List Int)) (sorted : (List Int)) (positions : (List Int)) (PreH1 : (i <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : ((Znth i input (0 : Int)) <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (n_pre >= INT_MIN)) (PreH6 : ((Znth i input (0 : Int)) >= INT_MIN)) (PreH7 : (i >= (0 : Int))) (PreH8 : ((0 : Int) <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((Zlength (input)) = n_pre)) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : ((Zlength (positions)) = 100)) (PreH13 : ((Zlength (bucket_ends)) = 100)) (PreH14 : ((Zlength (output_mixed)) = 100)) (PreH15 : ((-1) <= i)) (PreH16 : (i < n_pre)) (PreH17 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH18 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH19 : (Forall ((LE.le (α := Int)) ((0 : Int))) sorted)) (PreH20 : (Forall ((GT.gt (α := Int)) (100)) sorted)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions)) (PreH22 : (Forall ((GE.ge (α := Int)) (n_pre)) positions)) (PreH23 : ((i >= (0 : Int)) -> (1 <= (Znth (Znth i input (0 : Int)) positions (0 : Int))))) (PreH24 : (Forall (Eq (None)) (sublist (n_pre) (100) (output_mixed)))) (PreH25 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted i)) ,
  ((Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))) <= n_pre)

noncomputable def sort_entail_wit_9_split_goal_2 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (i : Int) (output_mixed : (List (Option Int))) (bucket_ends : (List Int)) (sorted : (List Int)) (positions : (List Int)) (PreH1 : (i <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : ((Znth i input (0 : Int)) <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (n_pre >= INT_MIN)) (PreH6 : ((Znth i input (0 : Int)) >= INT_MIN)) (PreH7 : (i >= (0 : Int))) (PreH8 : ((0 : Int) <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((Zlength (input)) = n_pre)) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : ((Zlength (positions)) = 100)) (PreH13 : ((Zlength (bucket_ends)) = 100)) (PreH14 : ((Zlength (output_mixed)) = 100)) (PreH15 : ((-1) <= i)) (PreH16 : (i < n_pre)) (PreH17 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH18 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH19 : (Forall ((LE.le (α := Int)) ((0 : Int))) sorted)) (PreH20 : (Forall ((GT.gt (α := Int)) (100)) sorted)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions)) (PreH22 : (Forall ((GE.ge (α := Int)) (n_pre)) positions)) (PreH23 : ((i >= (0 : Int)) -> (1 <= (Znth (Znth i input (0 : Int)) positions (0 : Int))))) (PreH24 : (Forall (Eq (None)) (sublist (n_pre) (100) (output_mixed)))) (PreH25 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted i)) ,
  ((Znth (i) (input) ((0 : Int))) < 100)

noncomputable def sort_entail_wit_9_split_goal_3 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (i : Int) (output_mixed : (List (Option Int))) (bucket_ends : (List Int)) (sorted : (List Int)) (positions : (List Int)) (PreH1 : (i <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : ((Znth i input (0 : Int)) <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (n_pre >= INT_MIN)) (PreH6 : ((Znth i input (0 : Int)) >= INT_MIN)) (PreH7 : (i >= (0 : Int))) (PreH8 : ((0 : Int) <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((Zlength (input)) = n_pre)) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : ((Zlength (positions)) = 100)) (PreH13 : ((Zlength (bucket_ends)) = 100)) (PreH14 : ((Zlength (output_mixed)) = 100)) (PreH15 : ((-1) <= i)) (PreH16 : (i < n_pre)) (PreH17 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH18 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH19 : (Forall ((LE.le (α := Int)) ((0 : Int))) sorted)) (PreH20 : (Forall ((GT.gt (α := Int)) (100)) sorted)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions)) (PreH22 : (Forall ((GE.ge (α := Int)) (n_pre)) positions)) (PreH23 : ((i >= (0 : Int)) -> (1 <= (Znth (Znth i input (0 : Int)) positions (0 : Int))))) (PreH24 : (Forall (Eq (None)) (sublist (n_pre) (100) (output_mixed)))) (PreH25 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted i)) ,
  ((0 : Int) <= (Znth (i) (input) ((0 : Int))))

noncomputable def sort_entail_wit_10 : Prop :=
  (
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (i : Int) (output_mixed : (List (Option Int))) (bucket_ends : (List Int)) (sorted : (List Int)) (positions : (List Int)) (PreH1 : ((0 : Int) <= (Znth (i) (input) ((0 : Int))))) (PreH2 : ((Znth (i) (input) ((0 : Int))) < 100)) (PreH3 : (1 <= (Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))))) (PreH4 : ((Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))) <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i >= (0 : Int))) (PreH8 : ((0 : Int) <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((Zlength (input)) = n_pre)) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : ((Zlength (positions)) = 100)) (PreH13 : ((Zlength (bucket_ends)) = 100)) (PreH14 : ((Zlength (output_mixed)) = 100)) (PreH15 : ((-1) <= i)) (PreH16 : (i < n_pre)) (PreH17 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH18 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH19 : (Forall ((LE.le (α := Int)) ((0 : Int))) sorted)) (PreH20 : (Forall ((GT.gt (α := Int)) (100)) sorted)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions)) (PreH22 : (Forall ((GE.ge (α := Int)) (n_pre)) positions)) (PreH23 : ((i >= (0 : Int)) -> (1 <= (Znth (Znth i input (0 : Int)) positions (0 : Int))))) (PreH24 : (Forall (Eq (None)) (sublist (n_pre) (100) (output_mixed)))) (PreH25 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted i)) ,
  (intArray.full ( &( "count" ) ) 100 (replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth (Znth (i) (input) ((0 : Int))) positions (0 : Int)) - 1)) (positions)))
  ** ((( &( "value" ) )) # Int |-> ((Znth (i) (input) ((0 : Int)))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
|--
  “ ((0 : Int) <= (Znth ((Znth (i) (input) ((0 : Int)))) ((replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))) - 1)) (positions))) ((0 : Int)))) ” &&
  “ ((Znth ((Znth (i) (input) ((0 : Int)))) ((replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))) - 1)) (positions))) ((0 : Int))) < 100) ” &&
  “ (i <= INT_MAX) ” &&
  “ (i >= INT_MIN) ” &&
  “ ((0 : Int) <= (Znth (i) (input) ((0 : Int)))) ” &&
  “ ((Znth (i) (input) ((0 : Int))) < 100) ” &&
  “ (1 <= (Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int)))) ” &&
  “ ((Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))) <= n_pre) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (i >= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (sorted)) = n_pre) ” &&
  “ ((Zlength (positions)) = 100) ” &&
  “ ((Zlength (bucket_ends)) = 100) ” &&
  “ ((Zlength (output_mixed)) = 100) ” &&
  “ ((-1) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) input) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) input) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) sorted) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) sorted) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) positions) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) positions) ” &&
  “ ((i >= (0 : Int)) -> (1 <= (Znth (Znth i input (0 : Int)) positions (0 : Int)))) ” &&
  “ (Forall (Eq (None)) (sublist (n_pre) (100) (output_mixed))) ” &&
  “ (CountingPlacementProgress input positions bucket_ends output_mixed sorted i) ”
  &&  ((( &( "value" ) )) # Int |-> ((Znth (i) (input) ((0 : Int)))))
  ** (intArray.full ( &( "count" ) ) 100 (replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth (Znth (i) (input) ((0 : Int))) positions (0 : Int)) - 1)) (positions)))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
) \/
(
forall (input : (List Int)) (n_pre : Int) (i : Int) (output_mixed : (List (Option Int))) (bucket_ends : (List Int)) (sorted : (List Int)) (positions : (List Int)) (PreH1 : (i <= INT_MAX)) (PreH2 : ((Znth (i) (input) ((0 : Int))) <= INT_MAX)) (PreH3 : (i >= INT_MIN)) (PreH4 : ((Znth (i) (input) ((0 : Int))) >= INT_MIN)) (PreH5 : ((0 : Int) <= (Znth (i) (input) ((0 : Int))))) (PreH6 : ((Znth (i) (input) ((0 : Int))) < 100)) (PreH7 : (1 <= (Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))))) (PreH8 : ((Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))) <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i >= (0 : Int))) (PreH12 : ((0 : Int) <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (sorted)) = n_pre)) (PreH16 : ((Zlength (positions)) = 100)) (PreH17 : ((Zlength (bucket_ends)) = 100)) (PreH18 : ((Zlength (output_mixed)) = 100)) (PreH19 : ((-1) <= i)) (PreH20 : (i < n_pre)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH22 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH23 : (Forall ((LE.le (α := Int)) ((0 : Int))) sorted)) (PreH24 : (Forall ((GT.gt (α := Int)) (100)) sorted)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions)) (PreH26 : (Forall ((GE.ge (α := Int)) (n_pre)) positions)) (PreH27 : ((i >= (0 : Int)) -> (1 <= (Znth (Znth i input (0 : Int)) positions (0 : Int))))) (PreH28 : (Forall (Eq (None)) (sublist (n_pre) (100) (output_mixed)))) (PreH29 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted i)) ,
  TT && emp 
|--
  “ ((Znth ((Znth (i) (input) ((0 : Int)))) ((replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))) - 1)) (positions))) ((0 : Int))) < 100) ” &&
  “ ((0 : Int) <= (Znth ((Znth (i) (input) ((0 : Int)))) ((replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))) - 1)) (positions))) ((0 : Int)))) ”
  &&  emp
)

noncomputable def sort_entail_wit_10_split_goal_1 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (i : Int) (output_mixed : (List (Option Int))) (bucket_ends : (List Int)) (sorted : (List Int)) (positions : (List Int)) (PreH1 : (i <= INT_MAX)) (PreH2 : ((Znth (i) (input) ((0 : Int))) <= INT_MAX)) (PreH3 : (i >= INT_MIN)) (PreH4 : ((Znth (i) (input) ((0 : Int))) >= INT_MIN)) (PreH5 : ((0 : Int) <= (Znth (i) (input) ((0 : Int))))) (PreH6 : ((Znth (i) (input) ((0 : Int))) < 100)) (PreH7 : (1 <= (Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))))) (PreH8 : ((Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))) <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i >= (0 : Int))) (PreH12 : ((0 : Int) <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (sorted)) = n_pre)) (PreH16 : ((Zlength (positions)) = 100)) (PreH17 : ((Zlength (bucket_ends)) = 100)) (PreH18 : ((Zlength (output_mixed)) = 100)) (PreH19 : ((-1) <= i)) (PreH20 : (i < n_pre)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH22 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH23 : (Forall ((LE.le (α := Int)) ((0 : Int))) sorted)) (PreH24 : (Forall ((GT.gt (α := Int)) (100)) sorted)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions)) (PreH26 : (Forall ((GE.ge (α := Int)) (n_pre)) positions)) (PreH27 : ((i >= (0 : Int)) -> (1 <= (Znth (Znth i input (0 : Int)) positions (0 : Int))))) (PreH28 : (Forall (Eq (None)) (sublist (n_pre) (100) (output_mixed)))) (PreH29 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted i)) ,
  ((Znth ((Znth (i) (input) ((0 : Int)))) ((replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))) - 1)) (positions))) ((0 : Int))) < 100)

noncomputable def sort_entail_wit_10_split_goal_2 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (i : Int) (output_mixed : (List (Option Int))) (bucket_ends : (List Int)) (sorted : (List Int)) (positions : (List Int)) (PreH1 : (i <= INT_MAX)) (PreH2 : ((Znth (i) (input) ((0 : Int))) <= INT_MAX)) (PreH3 : (i >= INT_MIN)) (PreH4 : ((Znth (i) (input) ((0 : Int))) >= INT_MIN)) (PreH5 : ((0 : Int) <= (Znth (i) (input) ((0 : Int))))) (PreH6 : ((Znth (i) (input) ((0 : Int))) < 100)) (PreH7 : (1 <= (Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))))) (PreH8 : ((Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))) <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i >= (0 : Int))) (PreH12 : ((0 : Int) <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (sorted)) = n_pre)) (PreH16 : ((Zlength (positions)) = 100)) (PreH17 : ((Zlength (bucket_ends)) = 100)) (PreH18 : ((Zlength (output_mixed)) = 100)) (PreH19 : ((-1) <= i)) (PreH20 : (i < n_pre)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH22 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH23 : (Forall ((LE.le (α := Int)) ((0 : Int))) sorted)) (PreH24 : (Forall ((GT.gt (α := Int)) (100)) sorted)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions)) (PreH26 : (Forall ((GE.ge (α := Int)) (n_pre)) positions)) (PreH27 : ((i >= (0 : Int)) -> (1 <= (Znth (Znth i input (0 : Int)) positions (0 : Int))))) (PreH28 : (Forall (Eq (None)) (sublist (n_pre) (100) (output_mixed)))) (PreH29 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted i)) ,
  ((0 : Int) <= (Znth ((Znth (i) (input) ((0 : Int)))) ((replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))) - 1)) (positions))) ((0 : Int))))

noncomputable def sort_entail_wit_11 : Prop :=
  (
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (i : Int) (output_mixed_2 : (List (Option Int))) (bucket_ends_2 : (List Int)) (sorted_2 : (List Int)) (positions_2 : (List Int)) (PreH1 : ((0 : Int) <= (Znth ((Znth (i) (input) ((0 : Int)))) ((replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth ((Znth (i) (input) ((0 : Int)))) (positions_2) ((0 : Int))) - 1)) (positions_2))) ((0 : Int))))) (PreH2 : ((Znth ((Znth (i) (input) ((0 : Int)))) ((replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth ((Znth (i) (input) ((0 : Int)))) (positions_2) ((0 : Int))) - 1)) (positions_2))) ((0 : Int))) < 100)) (PreH3 : (i <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : ((0 : Int) <= (Znth (i) (input) ((0 : Int))))) (PreH6 : ((Znth (i) (input) ((0 : Int))) < 100)) (PreH7 : (1 <= (Znth ((Znth (i) (input) ((0 : Int)))) (positions_2) ((0 : Int))))) (PreH8 : ((Znth ((Znth (i) (input) ((0 : Int)))) (positions_2) ((0 : Int))) <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i >= (0 : Int))) (PreH12 : ((0 : Int) <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (sorted_2)) = n_pre)) (PreH16 : ((Zlength (positions_2)) = 100)) (PreH17 : ((Zlength (bucket_ends_2)) = 100)) (PreH18 : ((Zlength (output_mixed_2)) = 100)) (PreH19 : ((-1) <= i)) (PreH20 : (i < n_pre)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH22 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH23 : (Forall ((LE.le (α := Int)) ((0 : Int))) sorted_2)) (PreH24 : (Forall ((GT.gt (α := Int)) (100)) sorted_2)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions_2)) (PreH26 : (Forall ((GE.ge (α := Int)) (n_pre)) positions_2)) (PreH27 : ((i >= (0 : Int)) -> (1 <= (Znth (Znth i input (0 : Int)) positions_2 (0 : Int))))) (PreH28 : (Forall (Eq (None)) (sublist (n_pre) (100) (output_mixed_2)))) (PreH29 : (CountingPlacementProgress input positions_2 bucket_ends_2 output_mixed_2 sorted_2 i)) ,
  (intArray.mixed_full ( &( "output" ) ) 100 (replace_Znth ((Znth (Znth (i) (input) ((0 : Int))) (replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth (Znth (i) (input) ((0 : Int))) positions_2 (0 : Int)) - 1)) (positions_2)) (0 : Int))) ((Some ((Znth (i) (input) ((0 : Int)))))) (output_mixed_2)))
  ** (intArray.full ( &( "count" ) ) 100 (replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth (Znth (i) (input) ((0 : Int))) positions_2 (0 : Int)) - 1)) (positions_2)))
  ** (intArray.full a_pre n_pre input)
|--
  EX output_mixed : (List (Option Int)), EX bucket_ends : (List Int), EX positions : (List Int), EX sorted : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (sorted)) = n_pre) ” &&
  “ ((Zlength (positions)) = 100) ” &&
  “ ((Zlength (bucket_ends)) = 100) ” &&
  “ ((Zlength (output_mixed)) = 100) ” &&
  “ ((-1) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) input) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) input) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) sorted) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) sorted) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) positions) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) positions) ” &&
  “ (((i - 1) >= (0 : Int)) -> (1 <= (Znth (Znth (i - 1) input (0 : Int)) positions (0 : Int)))) ” &&
  “ (Forall (Eq (None)) (sublist (n_pre) (100) (output_mixed))) ” &&
  “ (CountingPlacementProgress input positions bucket_ends output_mixed sorted (i - 1)) ”
  &&  (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
  ** (intArray.full ( &( "count" ) ) 100 positions)
) \/
(
forall (input : (List Int)) (n_pre : Int) (i : Int) (output_mixed_2 : (List (Option Int))) (bucket_ends_2 : (List Int)) (sorted_2 : (List Int)) (positions_2 : (List Int)) (PreH1 : ((0 : Int) <= (Znth ((Znth (i) (input) ((0 : Int)))) ((replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth ((Znth (i) (input) ((0 : Int)))) (positions_2) ((0 : Int))) - 1)) (positions_2))) ((0 : Int))))) (PreH2 : ((Znth ((Znth (i) (input) ((0 : Int)))) ((replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth ((Znth (i) (input) ((0 : Int)))) (positions_2) ((0 : Int))) - 1)) (positions_2))) ((0 : Int))) < 100)) (PreH3 : (i <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : ((0 : Int) <= (Znth (i) (input) ((0 : Int))))) (PreH6 : ((Znth (i) (input) ((0 : Int))) < 100)) (PreH7 : (1 <= (Znth ((Znth (i) (input) ((0 : Int)))) (positions_2) ((0 : Int))))) (PreH8 : ((Znth ((Znth (i) (input) ((0 : Int)))) (positions_2) ((0 : Int))) <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i >= (0 : Int))) (PreH12 : ((0 : Int) <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (sorted_2)) = n_pre)) (PreH16 : ((Zlength (positions_2)) = 100)) (PreH17 : ((Zlength (bucket_ends_2)) = 100)) (PreH18 : ((Zlength (output_mixed_2)) = 100)) (PreH19 : ((-1) <= i)) (PreH20 : (i < n_pre)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH22 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH23 : (Forall ((LE.le (α := Int)) ((0 : Int))) sorted_2)) (PreH24 : (Forall ((GT.gt (α := Int)) (100)) sorted_2)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions_2)) (PreH26 : (Forall ((GE.ge (α := Int)) (n_pre)) positions_2)) (PreH27 : ((i >= (0 : Int)) -> (1 <= (Znth (Znth i input (0 : Int)) positions_2 (0 : Int))))) (PreH28 : (Forall (Eq (None)) (sublist (n_pre) (100) (output_mixed_2)))) (PreH29 : (CountingPlacementProgress input positions_2 bucket_ends_2 output_mixed_2 sorted_2 i)) ,
  TT && emp 
|--
  EX bucket_ends : (List Int), EX sorted : (List Int),
  “ ((Zlength (sorted)) = (Zlength (input))) ” &&
  “ ((Zlength ((replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth (Znth (i) (input) ((0 : Int))) positions_2 (0 : Int)) - 1)) (positions_2)))) = 100) ” &&
  “ ((Zlength (bucket_ends)) = 100) ” &&
  “ ((Zlength ((replace_Znth ((Znth (Znth (i) (input) ((0 : Int))) (replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth (Znth (i) (input) ((0 : Int))) positions_2 (0 : Int)) - 1)) (positions_2)) (0 : Int))) ((Some ((Znth (i) (input) ((0 : Int)))))) (output_mixed_2)))) = 100) ” &&
  “ ((-1) <= (i - 1)) ” &&
  “ ((i - 1) < (Zlength (input))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) sorted) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) sorted) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth (Znth (i) (input) ((0 : Int))) positions_2 (0 : Int)) - 1)) (positions_2))) ” &&
  “ (Forall ((GE.ge (α := Int)) ((Zlength (input)))) (replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth (Znth (i) (input) ((0 : Int))) positions_2 (0 : Int)) - 1)) (positions_2))) ” &&
  “ (((i - 1) >= (0 : Int)) -> (1 <= (Znth (Znth (i - 1) input (0 : Int)) (replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth (Znth (i) (input) ((0 : Int))) positions_2 (0 : Int)) - 1)) (positions_2)) (0 : Int)))) ” &&
  “ (Forall (Eq (None)) (sublist ((Zlength (input))) (100) ((replace_Znth ((Znth (Znth (i) (input) ((0 : Int))) (replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth (Znth (i) (input) ((0 : Int))) positions_2 (0 : Int)) - 1)) (positions_2)) (0 : Int))) ((Some ((Znth (i) (input) ((0 : Int)))))) (output_mixed_2))))) ” &&
  “ (CountingPlacementProgress input (replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth (Znth (i) (input) ((0 : Int))) positions_2 (0 : Int)) - 1)) (positions_2)) bucket_ends (replace_Znth ((Znth (Znth (i) (input) ((0 : Int))) (replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth (Znth (i) (input) ((0 : Int))) positions_2 (0 : Int)) - 1)) (positions_2)) (0 : Int))) ((Some ((Znth (i) (input) ((0 : Int)))))) (output_mixed_2)) sorted (i - 1)) ”
  &&  emp
)

noncomputable def sort_entail_wit_12 : Prop :=
  (
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (i : Int) (output_mixed : (List (Option Int))) (bucket_ends : (List Int)) (positions : (List Int)) (sorted_2 : (List Int)) (PreH1 : (i < (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (sorted_2)) = n_pre)) (PreH6 : ((Zlength (positions)) = 100)) (PreH7 : ((Zlength (bucket_ends)) = 100)) (PreH8 : ((Zlength (output_mixed)) = 100)) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH12 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) sorted_2)) (PreH14 : (Forall ((GT.gt (α := Int)) (100)) sorted_2)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions)) (PreH16 : (Forall ((GE.ge (α := Int)) (n_pre)) positions)) (PreH17 : ((i >= (0 : Int)) -> (1 <= (Znth (Znth i input (0 : Int)) positions (0 : Int))))) (PreH18 : (Forall (Eq (None)) (sublist (n_pre) (100) (output_mixed)))) (PreH19 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted_2 i)) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
  ** (intArray.full ( &( "count" ) ) 100 positions)
|--
  EX bucket_starts : (List Int), EX live : (List Int), EX sorted : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (sorted)) = n_pre) ” &&
  “ ((Zlength (live)) = n_pre) ” &&
  “ ((Zlength (bucket_starts)) = 100) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) sorted) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) sorted) ” &&
  “ (CountingSorted input sorted) ” &&
  “ (CountingCopyProgress input sorted live (0 : Int)) ”
  &&  (intArray.full a_pre n_pre live)
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre sorted)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 100)
  ** (intArray.full ( &( "count" ) ) 100 bucket_starts)
) \/
(
forall (input : (List Int)) (n_pre : Int) (i : Int) (output_mixed : (List (Option Int))) (bucket_ends : (List Int)) (positions : (List Int)) (sorted_2 : (List Int)) (PreH1 : (i < (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (sorted_2)) = n_pre)) (PreH6 : ((Zlength (positions)) = 100)) (PreH7 : ((Zlength (bucket_ends)) = 100)) (PreH8 : ((Zlength (output_mixed)) = 100)) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH12 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) sorted_2)) (PreH14 : (Forall ((GT.gt (α := Int)) (100)) sorted_2)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions)) (PreH16 : (Forall ((GE.ge (α := Int)) (n_pre)) positions)) (PreH17 : ((i >= (0 : Int)) -> (1 <= (Znth (Znth i input (0 : Int)) positions (0 : Int))))) (PreH18 : (Forall (Eq (None)) (sublist (n_pre) (100) (output_mixed)))) (PreH19 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted_2 i)) ,
  (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
|--
  EX sorted : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (sorted)) = n_pre) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (positions)) = 100) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) sorted) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) sorted) ” &&
  “ (CountingSorted input sorted) ” &&
  “ (CountingCopyProgress input sorted input (0 : Int)) ”
  &&  (intArray.seg ( &( "output" ) ) (0 : Int) n_pre sorted)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 100)
)

noncomputable def sort_entail_wit_13 : Prop :=
  (
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (i : Int) (bucket_starts_2 : (List Int)) (live_2 : (List Int)) (sorted_2 : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (sorted_2)) = n_pre)) (PreH6 : ((Zlength (live_2)) = n_pre)) (PreH7 : ((Zlength (bucket_starts_2)) = 100)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) sorted_2)) (PreH11 : (Forall ((GT.gt (α := Int)) (100)) sorted_2)) (PreH12 : (CountingSorted input sorted_2)) (PreH13 : (CountingCopyProgress input sorted_2 live_2 i)) ,
  (intArray.full a_pre n_pre (replace_Znth (i) ((Znth (i - (0 : Int)) sorted_2 (0 : Int))) (live_2)))
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre sorted_2)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 100)
  ** (intArray.full ( &( "count" ) ) 100 bucket_starts_2)
|--
  EX bucket_starts : (List Int), EX live : (List Int), EX sorted : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (sorted)) = n_pre) ” &&
  “ ((Zlength (live)) = n_pre) ” &&
  “ ((Zlength (bucket_starts)) = 100) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) sorted) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) sorted) ” &&
  “ (CountingSorted input sorted) ” &&
  “ (CountingCopyProgress input sorted live (i + 1)) ”
  &&  (intArray.full a_pre n_pre live)
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre sorted)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 100)
  ** (intArray.full ( &( "count" ) ) 100 bucket_starts)
) \/
(
forall (input : (List Int)) (n_pre : Int) (i : Int) (bucket_starts_2 : (List Int)) (live_2 : (List Int)) (sorted_2 : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (sorted_2)) = n_pre)) (PreH6 : ((Zlength (live_2)) = n_pre)) (PreH7 : ((Zlength (bucket_starts_2)) = 100)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) sorted_2)) (PreH11 : (Forall ((GT.gt (α := Int)) (100)) sorted_2)) (PreH12 : (CountingSorted input sorted_2)) (PreH13 : (CountingCopyProgress input sorted_2 live_2 i)) ,
  TT && emp 
|--
  “ (CountingCopyProgress input sorted_2 (replace_Znth (i) ((Znth (i - (0 : Int)) sorted_2 (0 : Int))) (live_2)) (i + 1)) ” &&
  “ ((Zlength ((replace_Znth (i) ((Znth (i - (0 : Int)) sorted_2 (0 : Int))) (live_2)))) = n_pre) ”
  &&  emp
)

noncomputable def sort_entail_wit_13_split_goal_1 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (i : Int) (bucket_starts_2 : (List Int)) (live_2 : (List Int)) (sorted_2 : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (sorted_2)) = n_pre)) (PreH6 : ((Zlength (live_2)) = n_pre)) (PreH7 : ((Zlength (bucket_starts_2)) = 100)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) sorted_2)) (PreH11 : (Forall ((GT.gt (α := Int)) (100)) sorted_2)) (PreH12 : (CountingSorted input sorted_2)) (PreH13 : (CountingCopyProgress input sorted_2 live_2 i)) ,
  (CountingCopyProgress input sorted_2 (replace_Znth (i) ((Znth (i - (0 : Int)) sorted_2 (0 : Int))) (live_2)) (i + 1))

noncomputable def sort_entail_wit_13_split_goal_2 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (i : Int) (bucket_starts_2 : (List Int)) (live_2 : (List Int)) (sorted_2 : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (sorted_2)) = n_pre)) (PreH6 : ((Zlength (live_2)) = n_pre)) (PreH7 : ((Zlength (bucket_starts_2)) = 100)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) sorted_2)) (PreH11 : (Forall ((GT.gt (α := Int)) (100)) sorted_2)) (PreH12 : (CountingSorted input sorted_2)) (PreH13 : (CountingCopyProgress input sorted_2 live_2 i)) ,
  ((Zlength ((replace_Znth (i) ((Znth (i - (0 : Int)) sorted_2 (0 : Int))) (live_2)))) = n_pre)

noncomputable def sort_entail_wit_14 : Prop :=
  (
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (i : Int) (bucket_starts : (List Int)) (live : (List Int)) (sorted_2 : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (sorted_2)) = n_pre)) (PreH6 : ((Zlength (live)) = n_pre)) (PreH7 : ((Zlength (bucket_starts)) = 100)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) sorted_2)) (PreH11 : (Forall ((GT.gt (α := Int)) (100)) sorted_2)) (PreH12 : (CountingSorted input sorted_2)) (PreH13 : (CountingCopyProgress input sorted_2 live i)) ,
  (intArray.full a_pre n_pre live)
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre sorted_2)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 100)
  ** (intArray.full ( &( "count" ) ) 100 bucket_starts)
|--
  EX sorted : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (sorted)) = n_pre) ” &&
  “ (CountingSorted input sorted) ”
  &&  (intArray.full a_pre n_pre sorted)
  ** (intArray.undef_full ( &( "output" ) ) 100)
  ** (intArray.undef_full ( &( "count" ) ) 100)
) \/
(
forall (input : (List Int)) (n_pre : Int) (i : Int) (bucket_starts : (List Int)) (live : (List Int)) (sorted_2 : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (sorted_2)) = n_pre)) (PreH6 : ((Zlength (live)) = n_pre)) (PreH7 : ((Zlength (bucket_starts)) = 100)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) sorted_2)) (PreH11 : (Forall ((GT.gt (α := Int)) (100)) sorted_2)) (PreH12 : (CountingSorted input sorted_2)) (PreH13 : (CountingCopyProgress input sorted_2 live i)) ,
  (intArray.seg ( &( "output" ) ) (0 : Int) n_pre sorted_2)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 100)
  ** (intArray.full ( &( "count" ) ) 100 bucket_starts)
|--
  “ (CountingSorted input live) ”
  &&  (intArray.undef_full ( &( "output" ) ) 100)
  ** (intArray.undef_full ( &( "count" ) ) 100)
)

noncomputable def sort_entail_wit_14_split_goal_1 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (i : Int) (bucket_starts : (List Int)) (live : (List Int)) (sorted_2 : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (sorted_2)) = n_pre)) (PreH6 : ((Zlength (live)) = n_pre)) (PreH7 : ((Zlength (bucket_starts)) = 100)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) sorted_2)) (PreH11 : (Forall ((GT.gt (α := Int)) (100)) sorted_2)) (PreH12 : (CountingSorted input sorted_2)) (PreH13 : (CountingCopyProgress input sorted_2 live i)) ,
  (intArray.seg ( &( "output" ) ) (0 : Int) n_pre sorted_2)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 100)
  ** (intArray.full ( &( "count" ) ) 100 bucket_starts)
|--
  “ (CountingSorted input live) ”

noncomputable def sort_entail_wit_14_split_goal_spatial : Prop :=
  forall (input : (List Int)) (n_pre : Int) (i : Int) (bucket_starts : (List Int)) (live : (List Int)) (sorted_2 : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (sorted_2)) = n_pre)) (PreH6 : ((Zlength (live)) = n_pre)) (PreH7 : ((Zlength (bucket_starts)) = 100)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) sorted_2)) (PreH11 : (Forall ((GT.gt (α := Int)) (100)) sorted_2)) (PreH12 : (CountingSorted input sorted_2)) (PreH13 : (CountingCopyProgress input sorted_2 live i)) ,
  (intArray.seg ( &( "output" ) ) (0 : Int) n_pre sorted_2)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 100)
  ** (intArray.full ( &( "count" ) ) 100 bucket_starts)
|--
  (intArray.undef_full ( &( "output" ) ) 100)
  ** (intArray.undef_full ( &( "count" ) ) 100)

noncomputable def sort_return_wit_1 : Prop :=
  (
forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (sorted : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (sorted)) = n_pre)) (PreH5 : (CountingSorted input sorted)) ,
  (intArray.full a_pre n_pre sorted)
|--
  EX output : (List Int),
  “ (Permutation input output) ” &&
  “ (increasing output) ”
  &&  (intArray.full a_pre n_pre output)
) \/
(
forall (input : (List Int)) (n_pre : Int) (sorted : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (sorted)) = n_pre)) (PreH5 : (CountingSorted input sorted)) ,
  TT && emp 
|--
  “ (increasing sorted) ” &&
  “ (Permutation input sorted) ”
  &&  emp
)

noncomputable def sort_return_wit_1_split_goal_1 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (sorted : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (sorted)) = n_pre)) (PreH5 : (CountingSorted input sorted)) ,
  (increasing sorted)

noncomputable def sort_return_wit_1_split_goal_2 : Prop :=
  forall (input : (List Int)) (n_pre : Int) (sorted : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (sorted)) = n_pre)) (PreH5 : (CountingSorted input sorted)) ,
  (Permutation input sorted)

noncomputable def sort_partial_solve_wit_1 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (value : Int) (count_mixed : (List (Option Int))) (output_mixed : (List (Option Int))) (PreH1 : (value < 100)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed)) = 100)) (PreH6 : ((Zlength (count_mixed)) = 100)) (PreH7 : ((0 : Int) <= value)) (PreH8 : (value <= 100)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall (Eq (None)) output_mixed)) (PreH12 : (CountingZeroedPrefix count_mixed value)) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
  ** (intArray.mixed_full ( &( "count" ) ) 100 count_mixed)
|--
  “ (value < 100) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (output_mixed)) = 100) ” &&
  “ ((Zlength (count_mixed)) = 100) ” &&
  “ ((0 : Int) <= value) ” &&
  “ (value <= 100) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) input) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) input) ” &&
  “ (Forall (Eq (None)) output_mixed) ” &&
  “ (CountingZeroedPrefix count_mixed value) ”
  &&  (((( &( "count" ) ) + (value * sizeof(INT)))) # Int |->_)
  ** (intArray.mixed_missing_i ( &( "count" ) ) value (0 : Int) 100 count_mixed)
  ** (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)

noncomputable def sort_partial_solve_wit_2 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (i : Int) (output_mixed : (List (Option Int))) (counts : (List Int)) (PreH1 : ((0 : Int) <= (Znth i input (0 : Int)))) (PreH2 : ((Znth i input (0 : Int)) < 100)) (PreH3 : ((0 : Int) <= (Znth (Znth i input (0 : Int)) counts (0 : Int)))) (PreH4 : ((Znth (Znth i input (0 : Int)) counts (0 : Int)) < 100)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((Zlength (input)) = n_pre)) (PreH11 : ((Zlength (output_mixed)) = 100)) (PreH12 : ((Zlength (counts)) = 100)) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH16 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH17 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts)) (PreH18 : (Forall ((GE.ge (α := Int)) (i)) counts)) (PreH19 : (Forall (Eq (None)) output_mixed)) (PreH20 : (CountingHistogramPrefix input counts i)) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
  ** (intArray.full ( &( "count" ) ) 100 counts)
|--
  “ ((0 : Int) <= (Znth i input (0 : Int))) ” &&
  “ ((Znth i input (0 : Int)) < 100) ” &&
  “ ((0 : Int) <= (Znth (Znth i input (0 : Int)) counts (0 : Int))) ” &&
  “ ((Znth (Znth i input (0 : Int)) counts (0 : Int)) < 100) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (output_mixed)) = 100) ” &&
  “ ((Zlength (counts)) = 100) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) input) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) input) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts) ” &&
  “ (Forall ((GE.ge (α := Int)) (i)) counts) ” &&
  “ (Forall (Eq (None)) output_mixed) ” &&
  “ (CountingHistogramPrefix input counts i) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i input (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
  ** (intArray.full ( &( "count" ) ) 100 counts)

noncomputable def sort_partial_solve_wit_3 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (i : Int) (output_mixed : (List (Option Int))) (counts : (List Int)) (PreH1 : ((0 : Int) <= (Znth i input (0 : Int)))) (PreH2 : ((Znth i input (0 : Int)) < 100)) (PreH3 : ((0 : Int) <= (Znth (Znth i input (0 : Int)) counts (0 : Int)))) (PreH4 : ((Znth (Znth i input (0 : Int)) counts (0 : Int)) < 100)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((Zlength (input)) = n_pre)) (PreH11 : ((Zlength (output_mixed)) = 100)) (PreH12 : ((Zlength (counts)) = 100)) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH16 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH17 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts)) (PreH18 : (Forall ((GE.ge (α := Int)) (i)) counts)) (PreH19 : (Forall (Eq (None)) output_mixed)) (PreH20 : (CountingHistogramPrefix input counts i)) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
  ** (intArray.full ( &( "count" ) ) 100 counts)
|--
  “ ((0 : Int) <= (Znth i input (0 : Int))) ” &&
  “ ((Znth i input (0 : Int)) < 100) ” &&
  “ ((0 : Int) <= (Znth (Znth i input (0 : Int)) counts (0 : Int))) ” &&
  “ ((Znth (Znth i input (0 : Int)) counts (0 : Int)) < 100) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (output_mixed)) = 100) ” &&
  “ ((Zlength (counts)) = 100) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) input) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) input) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts) ” &&
  “ (Forall ((GE.ge (α := Int)) (i)) counts) ” &&
  “ (Forall (Eq (None)) output_mixed) ” &&
  “ (CountingHistogramPrefix input counts i) ”
  &&  (((( &( "count" ) ) + ((Znth i input (0 : Int)) * sizeof(INT)))) # Int |-> ((Znth (Znth i input (0 : Int)) counts (0 : Int))))
  ** (intArray.missing_i ( &( "count" ) ) (Znth i input (0 : Int)) (0 : Int) 100 counts)
  ** (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)

noncomputable def sort_partial_solve_wit_4 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (i : Int) (output_mixed : (List (Option Int))) (counts : (List Int)) (PreH1 : ((0 : Int) <= (Znth i input (0 : Int)))) (PreH2 : ((Znth i input (0 : Int)) < 100)) (PreH3 : ((0 : Int) <= (Znth (Znth i input (0 : Int)) counts (0 : Int)))) (PreH4 : ((Znth (Znth i input (0 : Int)) counts (0 : Int)) < 100)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((Zlength (input)) = n_pre)) (PreH11 : ((Zlength (output_mixed)) = 100)) (PreH12 : ((Zlength (counts)) = 100)) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH16 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH17 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts)) (PreH18 : (Forall ((GE.ge (α := Int)) (i)) counts)) (PreH19 : (Forall (Eq (None)) output_mixed)) (PreH20 : (CountingHistogramPrefix input counts i)) ,
  (intArray.full ( &( "count" ) ) 100 counts)
  ** (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
|--
  “ ((0 : Int) <= (Znth i input (0 : Int))) ” &&
  “ ((Znth i input (0 : Int)) < 100) ” &&
  “ ((0 : Int) <= (Znth (Znth i input (0 : Int)) counts (0 : Int))) ” &&
  “ ((Znth (Znth i input (0 : Int)) counts (0 : Int)) < 100) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (output_mixed)) = 100) ” &&
  “ ((Zlength (counts)) = 100) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) input) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) input) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts) ” &&
  “ (Forall ((GE.ge (α := Int)) (i)) counts) ” &&
  “ (Forall (Eq (None)) output_mixed) ” &&
  “ (CountingHistogramPrefix input counts i) ”
  &&  (((( &( "count" ) ) + ((Znth i input (0 : Int)) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i ( &( "count" ) ) (Znth i input (0 : Int)) (0 : Int) 100 counts)
  ** (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)

noncomputable def sort_partial_solve_wit_5 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (value : Int) (positions : (List Int)) (output_mixed : (List (Option Int))) (PreH1 : (value < 100)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed)) = 100)) (PreH6 : ((Zlength (positions)) = 100)) (PreH7 : (1 <= value)) (PreH8 : (value <= 100)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions)) (PreH12 : (Forall ((GE.ge (α := Int)) (n_pre)) positions)) (PreH13 : ((value < 100) -> (((Znth value positions (0 : Int)) + (Znth (value - 1) positions (0 : Int))) <= n_pre))) (PreH14 : (Forall (Eq (None)) output_mixed)) (PreH15 : (CountingCumulativeState input positions value)) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
  ** (intArray.full ( &( "count" ) ) 100 positions)
|--
  “ (value < 100) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (output_mixed)) = 100) ” &&
  “ ((Zlength (positions)) = 100) ” &&
  “ (1 <= value) ” &&
  “ (value <= 100) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) input) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) input) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) positions) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) positions) ” &&
  “ ((value < 100) -> (((Znth value positions (0 : Int)) + (Znth (value - 1) positions (0 : Int))) <= n_pre)) ” &&
  “ (Forall (Eq (None)) output_mixed) ” &&
  “ (CountingCumulativeState input positions value) ”
  &&  (((( &( "count" ) ) + (value * sizeof(INT)))) # Int |-> ((Znth value positions (0 : Int))))
  ** (intArray.missing_i ( &( "count" ) ) value (0 : Int) 100 positions)
  ** (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)

noncomputable def sort_partial_solve_wit_6 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (value : Int) (positions : (List Int)) (output_mixed : (List (Option Int))) (PreH1 : (value < 100)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed)) = 100)) (PreH6 : ((Zlength (positions)) = 100)) (PreH7 : (1 <= value)) (PreH8 : (value <= 100)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions)) (PreH12 : (Forall ((GE.ge (α := Int)) (n_pre)) positions)) (PreH13 : ((value < 100) -> (((Znth value positions (0 : Int)) + (Znth (value - 1) positions (0 : Int))) <= n_pre))) (PreH14 : (Forall (Eq (None)) output_mixed)) (PreH15 : (CountingCumulativeState input positions value)) ,
  (intArray.full ( &( "count" ) ) 100 positions)
  ** (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
|--
  “ (value < 100) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (output_mixed)) = 100) ” &&
  “ ((Zlength (positions)) = 100) ” &&
  “ (1 <= value) ” &&
  “ (value <= 100) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) input) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) input) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) positions) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) positions) ” &&
  “ ((value < 100) -> (((Znth value positions (0 : Int)) + (Znth (value - 1) positions (0 : Int))) <= n_pre)) ” &&
  “ (Forall (Eq (None)) output_mixed) ” &&
  “ (CountingCumulativeState input positions value) ”
  &&  (((( &( "count" ) ) + ((value - 1) * sizeof(INT)))) # Int |-> ((Znth (value - 1) positions (0 : Int))))
  ** (intArray.missing_i ( &( "count" ) ) (value - 1) (0 : Int) 100 positions)
  ** (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)

noncomputable def sort_partial_solve_wit_7 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (value : Int) (positions : (List Int)) (output_mixed : (List (Option Int))) (PreH1 : (value < 100)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (output_mixed)) = 100)) (PreH6 : ((Zlength (positions)) = 100)) (PreH7 : (1 <= value)) (PreH8 : (value <= 100)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions)) (PreH12 : (Forall ((GE.ge (α := Int)) (n_pre)) positions)) (PreH13 : ((value < 100) -> (((Znth value positions (0 : Int)) + (Znth (value - 1) positions (0 : Int))) <= n_pre))) (PreH14 : (Forall (Eq (None)) output_mixed)) (PreH15 : (CountingCumulativeState input positions value)) ,
  (intArray.full ( &( "count" ) ) 100 positions)
  ** (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
|--
  “ (value < 100) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (output_mixed)) = 100) ” &&
  “ ((Zlength (positions)) = 100) ” &&
  “ (1 <= value) ” &&
  “ (value <= 100) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) input) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) input) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) positions) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) positions) ” &&
  “ ((value < 100) -> (((Znth value positions (0 : Int)) + (Znth (value - 1) positions (0 : Int))) <= n_pre)) ” &&
  “ (Forall (Eq (None)) output_mixed) ” &&
  “ (CountingCumulativeState input positions value) ”
  &&  (((( &( "count" ) ) + (value * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i ( &( "count" ) ) value (0 : Int) 100 positions)
  ** (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)

noncomputable def sort_partial_solve_wit_8 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (i : Int) (output_mixed : (List (Option Int))) (bucket_ends : (List Int)) (sorted : (List Int)) (positions : (List Int)) (PreH1 : (i >= (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : ((Zlength (positions)) = 100)) (PreH7 : ((Zlength (bucket_ends)) = 100)) (PreH8 : ((Zlength (output_mixed)) = 100)) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH12 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) sorted)) (PreH14 : (Forall ((GT.gt (α := Int)) (100)) sorted)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions)) (PreH16 : (Forall ((GE.ge (α := Int)) (n_pre)) positions)) (PreH17 : ((i >= (0 : Int)) -> (1 <= (Znth (Znth i input (0 : Int)) positions (0 : Int))))) (PreH18 : (Forall (Eq (None)) (sublist (n_pre) (100) (output_mixed)))) (PreH19 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted i)) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
  ** (intArray.full ( &( "count" ) ) 100 positions)
|--
  “ (i >= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (sorted)) = n_pre) ” &&
  “ ((Zlength (positions)) = 100) ” &&
  “ ((Zlength (bucket_ends)) = 100) ” &&
  “ ((Zlength (output_mixed)) = 100) ” &&
  “ ((-1) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) input) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) input) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) sorted) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) sorted) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) positions) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) positions) ” &&
  “ ((i >= (0 : Int)) -> (1 <= (Znth (Znth i input (0 : Int)) positions (0 : Int)))) ” &&
  “ (Forall (Eq (None)) (sublist (n_pre) (100) (output_mixed))) ” &&
  “ (CountingPlacementProgress input positions bucket_ends output_mixed sorted i) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i input (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
  ** (intArray.full ( &( "count" ) ) 100 positions)

noncomputable def sort_partial_solve_wit_9 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (i : Int) (output_mixed : (List (Option Int))) (bucket_ends : (List Int)) (sorted : (List Int)) (positions : (List Int)) (PreH1 : ((0 : Int) <= (Znth (i) (input) ((0 : Int))))) (PreH2 : ((Znth (i) (input) ((0 : Int))) < 100)) (PreH3 : ((Znth (i) (input) ((0 : Int))) = (Znth (i) (input) ((0 : Int))))) (PreH4 : (1 <= (Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))))) (PreH5 : ((Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))) <= n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i >= (0 : Int))) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : ((Zlength (input)) = n_pre)) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : ((Zlength (positions)) = 100)) (PreH14 : ((Zlength (bucket_ends)) = 100)) (PreH15 : ((Zlength (output_mixed)) = 100)) (PreH16 : ((-1) <= i)) (PreH17 : (i < n_pre)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH19 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) sorted)) (PreH21 : (Forall ((GT.gt (α := Int)) (100)) sorted)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions)) (PreH23 : (Forall ((GE.ge (α := Int)) (n_pre)) positions)) (PreH24 : ((i >= (0 : Int)) -> (1 <= (Znth (Znth i input (0 : Int)) positions (0 : Int))))) (PreH25 : (Forall (Eq (None)) (sublist (n_pre) (100) (output_mixed)))) (PreH26 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted i)) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
  ** (intArray.full ( &( "count" ) ) 100 positions)
|--
  “ ((0 : Int) <= (Znth (i) (input) ((0 : Int)))) ” &&
  “ ((Znth (i) (input) ((0 : Int))) < 100) ” &&
  “ (1 <= (Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int)))) ” &&
  “ ((Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))) <= n_pre) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (i >= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (sorted)) = n_pre) ” &&
  “ ((Zlength (positions)) = 100) ” &&
  “ ((Zlength (bucket_ends)) = 100) ” &&
  “ ((Zlength (output_mixed)) = 100) ” &&
  “ ((-1) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) input) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) input) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) sorted) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) sorted) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) positions) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) positions) ” &&
  “ ((i >= (0 : Int)) -> (1 <= (Znth (Znth i input (0 : Int)) positions (0 : Int)))) ” &&
  “ (Forall (Eq (None)) (sublist (n_pre) (100) (output_mixed))) ” &&
  “ (CountingPlacementProgress input positions bucket_ends output_mixed sorted i) ”
  &&  (((( &( "count" ) ) + ((Znth (i) (input) ((0 : Int))) * sizeof(INT)))) # Int |-> ((Znth (Znth (i) (input) ((0 : Int))) positions (0 : Int))))
  ** (intArray.missing_i ( &( "count" ) ) (Znth (i) (input) ((0 : Int))) (0 : Int) 100 positions)
  ** (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)

noncomputable def sort_partial_solve_wit_10 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (i : Int) (output_mixed : (List (Option Int))) (bucket_ends : (List Int)) (sorted : (List Int)) (positions : (List Int)) (PreH1 : ((0 : Int) <= (Znth (i) (input) ((0 : Int))))) (PreH2 : ((Znth (i) (input) ((0 : Int))) < 100)) (PreH3 : (1 <= (Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))))) (PreH4 : ((Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))) <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i >= (0 : Int))) (PreH8 : ((0 : Int) <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((Zlength (input)) = n_pre)) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : ((Zlength (positions)) = 100)) (PreH13 : ((Zlength (bucket_ends)) = 100)) (PreH14 : ((Zlength (output_mixed)) = 100)) (PreH15 : ((-1) <= i)) (PreH16 : (i < n_pre)) (PreH17 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH18 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH19 : (Forall ((LE.le (α := Int)) ((0 : Int))) sorted)) (PreH20 : (Forall ((GT.gt (α := Int)) (100)) sorted)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions)) (PreH22 : (Forall ((GE.ge (α := Int)) (n_pre)) positions)) (PreH23 : ((i >= (0 : Int)) -> (1 <= (Znth (Znth i input (0 : Int)) positions (0 : Int))))) (PreH24 : (Forall (Eq (None)) (sublist (n_pre) (100) (output_mixed)))) (PreH25 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted i)) ,
  (intArray.full ( &( "count" ) ) 100 positions)
  ** (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
|--
  “ ((0 : Int) <= (Znth (i) (input) ((0 : Int)))) ” &&
  “ ((Znth (i) (input) ((0 : Int))) < 100) ” &&
  “ (1 <= (Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int)))) ” &&
  “ ((Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))) <= n_pre) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (i >= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (sorted)) = n_pre) ” &&
  “ ((Zlength (positions)) = 100) ” &&
  “ ((Zlength (bucket_ends)) = 100) ” &&
  “ ((Zlength (output_mixed)) = 100) ” &&
  “ ((-1) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) input) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) input) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) sorted) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) sorted) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) positions) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) positions) ” &&
  “ ((i >= (0 : Int)) -> (1 <= (Znth (Znth i input (0 : Int)) positions (0 : Int)))) ” &&
  “ (Forall (Eq (None)) (sublist (n_pre) (100) (output_mixed))) ” &&
  “ (CountingPlacementProgress input positions bucket_ends output_mixed sorted i) ”
  &&  (((( &( "count" ) ) + ((Znth (i) (input) ((0 : Int))) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i ( &( "count" ) ) (Znth (i) (input) ((0 : Int))) (0 : Int) 100 positions)
  ** (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)

noncomputable def sort_partial_solve_wit_11 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (i : Int) (output_mixed : (List (Option Int))) (bucket_ends : (List Int)) (sorted : (List Int)) (positions : (List Int)) (PreH1 : ((0 : Int) <= (Znth ((Znth (i) (input) ((0 : Int)))) ((replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))) - 1)) (positions))) ((0 : Int))))) (PreH2 : ((Znth ((Znth (i) (input) ((0 : Int)))) ((replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))) - 1)) (positions))) ((0 : Int))) < 100)) (PreH3 : (i <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : ((0 : Int) <= (Znth (i) (input) ((0 : Int))))) (PreH6 : ((Znth (i) (input) ((0 : Int))) < 100)) (PreH7 : (1 <= (Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))))) (PreH8 : ((Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))) <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i >= (0 : Int))) (PreH12 : ((0 : Int) <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (sorted)) = n_pre)) (PreH16 : ((Zlength (positions)) = 100)) (PreH17 : ((Zlength (bucket_ends)) = 100)) (PreH18 : ((Zlength (output_mixed)) = 100)) (PreH19 : ((-1) <= i)) (PreH20 : (i < n_pre)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH22 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH23 : (Forall ((LE.le (α := Int)) ((0 : Int))) sorted)) (PreH24 : (Forall ((GT.gt (α := Int)) (100)) sorted)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions)) (PreH26 : (Forall ((GE.ge (α := Int)) (n_pre)) positions)) (PreH27 : ((i >= (0 : Int)) -> (1 <= (Znth (Znth i input (0 : Int)) positions (0 : Int))))) (PreH28 : (Forall (Eq (None)) (sublist (n_pre) (100) (output_mixed)))) (PreH29 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted i)) ,
  (intArray.full ( &( "count" ) ) 100 (replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth (Znth (i) (input) ((0 : Int))) positions (0 : Int)) - 1)) (positions)))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
|--
  “ ((0 : Int) <= (Znth ((Znth (i) (input) ((0 : Int)))) ((replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))) - 1)) (positions))) ((0 : Int)))) ” &&
  “ ((Znth ((Znth (i) (input) ((0 : Int)))) ((replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))) - 1)) (positions))) ((0 : Int))) < 100) ” &&
  “ (i <= INT_MAX) ” &&
  “ (i >= INT_MIN) ” &&
  “ ((0 : Int) <= (Znth (i) (input) ((0 : Int)))) ” &&
  “ ((Znth (i) (input) ((0 : Int))) < 100) ” &&
  “ (1 <= (Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int)))) ” &&
  “ ((Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))) <= n_pre) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (i >= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (sorted)) = n_pre) ” &&
  “ ((Zlength (positions)) = 100) ” &&
  “ ((Zlength (bucket_ends)) = 100) ” &&
  “ ((Zlength (output_mixed)) = 100) ” &&
  “ ((-1) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) input) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) input) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) sorted) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) sorted) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) positions) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) positions) ” &&
  “ ((i >= (0 : Int)) -> (1 <= (Znth (Znth i input (0 : Int)) positions (0 : Int)))) ” &&
  “ (Forall (Eq (None)) (sublist (n_pre) (100) (output_mixed))) ” &&
  “ (CountingPlacementProgress input positions bucket_ends output_mixed sorted i) ”
  &&  (((( &( "count" ) ) + ((Znth (i) (input) ((0 : Int))) * sizeof(INT)))) # Int |-> ((Znth (Znth (i) (input) ((0 : Int))) (replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth (Znth (i) (input) ((0 : Int))) positions (0 : Int)) - 1)) (positions)) (0 : Int))))
  ** (intArray.missing_i ( &( "count" ) ) (Znth (i) (input) ((0 : Int))) (0 : Int) 100 (replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth (Znth (i) (input) ((0 : Int))) positions (0 : Int)) - 1)) (positions)))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)

noncomputable def sort_partial_solve_wit_12 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (i : Int) (output_mixed : (List (Option Int))) (bucket_ends : (List Int)) (sorted : (List Int)) (positions : (List Int)) (PreH1 : ((0 : Int) <= (Znth ((Znth (i) (input) ((0 : Int)))) ((replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))) - 1)) (positions))) ((0 : Int))))) (PreH2 : ((Znth ((Znth (i) (input) ((0 : Int)))) ((replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))) - 1)) (positions))) ((0 : Int))) < 100)) (PreH3 : (i <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : ((0 : Int) <= (Znth (i) (input) ((0 : Int))))) (PreH6 : ((Znth (i) (input) ((0 : Int))) < 100)) (PreH7 : (1 <= (Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))))) (PreH8 : ((Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))) <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i >= (0 : Int))) (PreH12 : ((0 : Int) <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (sorted)) = n_pre)) (PreH16 : ((Zlength (positions)) = 100)) (PreH17 : ((Zlength (bucket_ends)) = 100)) (PreH18 : ((Zlength (output_mixed)) = 100)) (PreH19 : ((-1) <= i)) (PreH20 : (i < n_pre)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH22 : (Forall ((GT.gt (α := Int)) (100)) input)) (PreH23 : (Forall ((LE.le (α := Int)) ((0 : Int))) sorted)) (PreH24 : (Forall ((GT.gt (α := Int)) (100)) sorted)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) positions)) (PreH26 : (Forall ((GE.ge (α := Int)) (n_pre)) positions)) (PreH27 : ((i >= (0 : Int)) -> (1 <= (Znth (Znth i input (0 : Int)) positions (0 : Int))))) (PreH28 : (Forall (Eq (None)) (sublist (n_pre) (100) (output_mixed)))) (PreH29 : (CountingPlacementProgress input positions bucket_ends output_mixed sorted i)) ,
  (intArray.full ( &( "count" ) ) 100 (replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth (Znth (i) (input) ((0 : Int))) positions (0 : Int)) - 1)) (positions)))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.mixed_full ( &( "output" ) ) 100 output_mixed)
|--
  “ ((0 : Int) <= (Znth ((Znth (i) (input) ((0 : Int)))) ((replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))) - 1)) (positions))) ((0 : Int)))) ” &&
  “ ((Znth ((Znth (i) (input) ((0 : Int)))) ((replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))) - 1)) (positions))) ((0 : Int))) < 100) ” &&
  “ (i <= INT_MAX) ” &&
  “ (i >= INT_MIN) ” &&
  “ ((0 : Int) <= (Znth (i) (input) ((0 : Int)))) ” &&
  “ ((Znth (i) (input) ((0 : Int))) < 100) ” &&
  “ (1 <= (Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int)))) ” &&
  “ ((Znth ((Znth (i) (input) ((0 : Int)))) (positions) ((0 : Int))) <= n_pre) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (i >= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (sorted)) = n_pre) ” &&
  “ ((Zlength (positions)) = 100) ” &&
  “ ((Zlength (bucket_ends)) = 100) ” &&
  “ ((Zlength (output_mixed)) = 100) ” &&
  “ ((-1) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) input) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) input) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) sorted) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) sorted) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) positions) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) positions) ” &&
  “ ((i >= (0 : Int)) -> (1 <= (Znth (Znth i input (0 : Int)) positions (0 : Int)))) ” &&
  “ (Forall (Eq (None)) (sublist (n_pre) (100) (output_mixed))) ” &&
  “ (CountingPlacementProgress input positions bucket_ends output_mixed sorted i) ”
  &&  (((( &( "output" ) ) + ((Znth (Znth (i) (input) ((0 : Int))) (replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth (Znth (i) (input) ((0 : Int))) positions (0 : Int)) - 1)) (positions)) (0 : Int)) * sizeof(INT)))) # Int |->_)
  ** (intArray.mixed_missing_i ( &( "output" ) ) (Znth (Znth (i) (input) ((0 : Int))) (replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth (Znth (i) (input) ((0 : Int))) positions (0 : Int)) - 1)) (positions)) (0 : Int)) (0 : Int) 100 output_mixed)
  ** (intArray.full ( &( "count" ) ) 100 (replace_Znth ((Znth (i) (input) ((0 : Int)))) (((Znth (Znth (i) (input) ((0 : Int))) positions (0 : Int)) - 1)) (positions)))
  ** (intArray.full a_pre n_pre input)

noncomputable def sort_partial_solve_wit_13 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (i : Int) (bucket_starts : (List Int)) (live : (List Int)) (sorted : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : ((Zlength (live)) = n_pre)) (PreH7 : ((Zlength (bucket_starts)) = 100)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) sorted)) (PreH11 : (Forall ((GT.gt (α := Int)) (100)) sorted)) (PreH12 : (CountingSorted input sorted)) (PreH13 : (CountingCopyProgress input sorted live i)) ,
  (intArray.full a_pre n_pre live)
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre sorted)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 100)
  ** (intArray.full ( &( "count" ) ) 100 bucket_starts)
|--
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (sorted)) = n_pre) ” &&
  “ ((Zlength (live)) = n_pre) ” &&
  “ ((Zlength (bucket_starts)) = 100) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) sorted) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) sorted) ” &&
  “ (CountingSorted input sorted) ” &&
  “ (CountingCopyProgress input sorted live i) ”
  &&  (((( &( "output" ) ) + (i * sizeof(INT)))) # Int |-> ((Znth (i - (0 : Int)) sorted (0 : Int))))
  ** (intArray.missing_i ( &( "output" ) ) i (0 : Int) n_pre sorted)
  ** (intArray.full a_pre n_pre live)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 100)
  ** (intArray.full ( &( "count" ) ) 100 bucket_starts)

noncomputable def sort_partial_solve_wit_14 : Prop :=
  forall (input : (List Int)) (a_pre : Int) (n_pre : Int) (i : Int) (bucket_starts : (List Int)) (live : (List Int)) (sorted : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : ((Zlength (live)) = n_pre)) (PreH7 : ((Zlength (bucket_starts)) = 100)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) sorted)) (PreH11 : (Forall ((GT.gt (α := Int)) (100)) sorted)) (PreH12 : (CountingSorted input sorted)) (PreH13 : (CountingCopyProgress input sorted live i)) ,
  (intArray.seg ( &( "output" ) ) (0 : Int) n_pre sorted)
  ** (intArray.full a_pre n_pre live)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 100)
  ** (intArray.full ( &( "count" ) ) 100 bucket_starts)
|--
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (sorted)) = n_pre) ” &&
  “ ((Zlength (live)) = n_pre) ” &&
  “ ((Zlength (bucket_starts)) = 100) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) sorted) ” &&
  “ (Forall ((GT.gt (α := Int)) (100)) sorted) ” &&
  “ (CountingSorted input sorted) ” &&
  “ (CountingCopyProgress input sorted live i) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i a_pre i (0 : Int) n_pre live)
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre sorted)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 100)
  ** (intArray.full ( &( "count" ) ) 100 bucket_starts)


structure VC_Correct : Type where
  proof_of_sort_safety_wit_1 : sort_safety_wit_1
  proof_of_sort_safety_wit_2 : sort_safety_wit_2
  proof_of_sort_safety_wit_3 : sort_safety_wit_3
  proof_of_sort_safety_wit_4 : sort_safety_wit_4
  proof_of_sort_safety_wit_5 : sort_safety_wit_5
  proof_of_sort_safety_wit_6 : sort_safety_wit_6
  proof_of_sort_safety_wit_7 : sort_safety_wit_7
  proof_of_sort_safety_wit_8 : sort_safety_wit_8
  proof_of_sort_safety_wit_9 : sort_safety_wit_9
  proof_of_sort_safety_wit_11 : sort_safety_wit_11
  proof_of_sort_safety_wit_12 : sort_safety_wit_12
  proof_of_sort_safety_wit_13 : sort_safety_wit_13
  proof_of_sort_safety_wit_14 : sort_safety_wit_14
  proof_of_sort_safety_wit_15 : sort_safety_wit_15
  proof_of_sort_safety_wit_16 : sort_safety_wit_16
  proof_of_sort_safety_wit_17 : sort_safety_wit_17
  proof_of_sort_safety_wit_18 : sort_safety_wit_18
  proof_of_sort_safety_wit_19 : sort_safety_wit_19
  proof_of_sort_safety_wit_20 : sort_safety_wit_20
  proof_of_sort_partial_solve_wit_1 : sort_partial_solve_wit_1
  proof_of_sort_partial_solve_wit_2 : sort_partial_solve_wit_2
  proof_of_sort_partial_solve_wit_3 : sort_partial_solve_wit_3
  proof_of_sort_partial_solve_wit_4 : sort_partial_solve_wit_4
  proof_of_sort_partial_solve_wit_5 : sort_partial_solve_wit_5
  proof_of_sort_partial_solve_wit_6 : sort_partial_solve_wit_6
  proof_of_sort_partial_solve_wit_7 : sort_partial_solve_wit_7
  proof_of_sort_partial_solve_wit_8 : sort_partial_solve_wit_8
  proof_of_sort_partial_solve_wit_9 : sort_partial_solve_wit_9
  proof_of_sort_partial_solve_wit_10 : sort_partial_solve_wit_10
  proof_of_sort_partial_solve_wit_11 : sort_partial_solve_wit_11
  proof_of_sort_partial_solve_wit_12 : sort_partial_solve_wit_12
  proof_of_sort_partial_solve_wit_13 : sort_partial_solve_wit_13
  proof_of_sort_partial_solve_wit_14 : sort_partial_solve_wit_14
  proof_of_sort_safety_wit_10 : sort_safety_wit_10
  proof_of_sort_entail_wit_1 : sort_entail_wit_1
  proof_of_sort_entail_wit_2 : sort_entail_wit_2
  proof_of_sort_entail_wit_3 : sort_entail_wit_3
  proof_of_sort_entail_wit_4 : sort_entail_wit_4
  proof_of_sort_entail_wit_5 : sort_entail_wit_5
  proof_of_sort_entail_wit_6 : sort_entail_wit_6
  proof_of_sort_entail_wit_7 : sort_entail_wit_7
  proof_of_sort_entail_wit_8 : sort_entail_wit_8
  proof_of_sort_entail_wit_9 : sort_entail_wit_9
  proof_of_sort_entail_wit_10 : sort_entail_wit_10
  proof_of_sort_entail_wit_11 : sort_entail_wit_11
  proof_of_sort_entail_wit_12 : sort_entail_wit_12
  proof_of_sort_entail_wit_13 : sort_entail_wit_13
  proof_of_sort_entail_wit_14 : sort_entail_wit_14
  proof_of_sort_return_wit_1 : sort_return_wit_1

end SimpleC.EE.LLM_bench.Algorithms.counting_sort.counting_sort_goal
