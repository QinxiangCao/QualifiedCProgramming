import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance concatenating_numbers_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def quicksort_numbers_safety_wit_1 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : ((0 : Int) <= low_pre)) (PreH6 : (low_pre <= count_pre)) (PreH7 : ((-1) <= high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : ((Zlength (rows)) = count_pre)) (PreH12 : ((Zlength (lens)) = count_pre)) (PreH13 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows)))) (PreH14 : (Forall ((LE.le (α := Int)) (1)) lens)) (PreH15 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens)) (PreH16 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH17 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows) (lens)))) (PreH19 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows) (lens)))) (PreH20 : (FlatRows flat rows count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat)
  ** (intArray.full lengths_pre count_pre lens)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def quicksort_numbers_safety_wit_2 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : ((0 : Int) > low_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre <= count_pre)) (PreH8 : ((-1) <= high_pre)) (PreH9 : (high_pre < count_pre)) (PreH10 : (1 <= (sum (lens)))) (PreH11 : ((sum (lens)) <= 200)) (PreH12 : ((Zlength (rows)) = count_pre)) (PreH13 : ((Zlength (lens)) = count_pre)) (PreH14 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows)))) (PreH15 : (Forall ((LE.le (α := Int)) (1)) lens)) (PreH16 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens)) (PreH17 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH18 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH19 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows) (lens)))) (PreH20 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows) (lens)))) (PreH21 : (FlatRows flat rows count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat)
  ** (intArray.full lengths_pre count_pre lens)
|--
  “ False ”

noncomputable def quicksort_numbers_safety_wit_3 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (high_pre >= count_pre)) (PreH2 : (low_pre < high_pre)) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : ((0 : Int) <= low_pre)) (PreH9 : (low_pre <= count_pre)) (PreH10 : ((-1) <= high_pre)) (PreH11 : (high_pre < count_pre)) (PreH12 : (1 <= (sum (lens)))) (PreH13 : ((sum (lens)) <= 200)) (PreH14 : ((Zlength (rows)) = count_pre)) (PreH15 : ((Zlength (lens)) = count_pre)) (PreH16 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows)))) (PreH17 : (Forall ((LE.le (α := Int)) (1)) lens)) (PreH18 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens)) (PreH19 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH20 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows) (lens)))) (PreH22 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows) (lens)))) (PreH23 : (FlatRows flat rows count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat)
  ** (intArray.full lengths_pre count_pre lens)
|--
  “ False ”

noncomputable def quicksort_numbers_safety_wit_4 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (high_pre < count_pre)) (PreH2 : (low_pre < high_pre)) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : ((0 : Int) <= low_pre)) (PreH9 : (low_pre <= count_pre)) (PreH10 : ((-1) <= high_pre)) (PreH11 : (high_pre < count_pre)) (PreH12 : (1 <= (sum (lens)))) (PreH13 : ((sum (lens)) <= 200)) (PreH14 : ((Zlength (rows)) = count_pre)) (PreH15 : ((Zlength (lens)) = count_pre)) (PreH16 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows)))) (PreH17 : (Forall ((LE.le (α := Int)) (1)) lens)) (PreH18 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens)) (PreH19 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH20 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows) (lens)))) (PreH22 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows) (lens)))) (PreH23 : (FlatRows flat rows count_pre number_width_pre)) ,
  ((( &( "boundary" ) )) # Int |->_)
  ** (intArray.full lengths_pre count_pre lens)
  ** ((( &( "pivot_length" ) )) # Int |-> ((Znth high_pre lens (0 : Int))))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat)
|--
  “ ((low_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (low_pre - 1)) ”

noncomputable def quicksort_numbers_safety_wit_5 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (high_pre < count_pre)) (PreH2 : (low_pre < high_pre)) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : ((0 : Int) <= low_pre)) (PreH9 : (low_pre <= count_pre)) (PreH10 : ((-1) <= high_pre)) (PreH11 : (high_pre < count_pre)) (PreH12 : (1 <= (sum (lens)))) (PreH13 : ((sum (lens)) <= 200)) (PreH14 : ((Zlength (rows)) = count_pre)) (PreH15 : ((Zlength (lens)) = count_pre)) (PreH16 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows)))) (PreH17 : (Forall ((LE.le (α := Int)) (1)) lens)) (PreH18 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens)) (PreH19 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH20 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows) (lens)))) (PreH22 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows) (lens)))) (PreH23 : (FlatRows flat rows count_pre number_width_pre)) ,
  ((( &( "boundary" ) )) # Int |->_)
  ** (intArray.full lengths_pre count_pre lens)
  ** ((( &( "pivot_length" ) )) # Int |-> ((Znth high_pre lens (0 : Int))))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def quicksort_numbers_safety_wit_6 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : (scan < high_pre)) (PreH2 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH3 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : ((0 : Int) <= low_pre)) (PreH9 : (low_pre < high_pre)) (PreH10 : (high_pre < count_pre)) (PreH11 : ((low_pre - 1) <= boundary)) (PreH12 : (boundary < scan)) (PreH13 : (low_pre <= scan)) (PreH14 : (scan <= high_pre)) (PreH15 : (1 <= (sum (lens)))) (PreH16 : ((sum (lens)) <= 200)) (PreH17 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH18 : (1 <= pivot_length)) (PreH19 : (pivot_length <= number_width_pre)) (PreH20 : ((Zlength (rows1)) = count_pre)) (PreH21 : ((Zlength (lens1)) = count_pre)) (PreH22 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH23 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH24 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH25 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH26 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH27 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH29 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "total_length" ) )) # Int |->_)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |-> ((Znth scan lens1 (0 : Int))))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ (((Znth scan lens1 (0 : Int)) + pivot_length) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth scan lens1 (0 : Int)) + pivot_length)) ”
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : (scan < high_pre)) (PreH2 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH3 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : ((0 : Int) <= low_pre)) (PreH9 : (low_pre < high_pre)) (PreH10 : (high_pre < count_pre)) (PreH11 : ((low_pre - 1) <= boundary)) (PreH12 : (boundary < scan)) (PreH13 : (low_pre <= scan)) (PreH14 : (scan <= high_pre)) (PreH15 : (1 <= (sum (lens)))) (PreH16 : ((sum (lens)) <= 200)) (PreH17 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH18 : (1 <= pivot_length)) (PreH19 : (pivot_length <= number_width_pre)) (PreH20 : ((Zlength (rows1)) = count_pre)) (PreH21 : ((Zlength (lens1)) = count_pre)) (PreH22 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH23 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH24 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH25 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH26 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH27 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH29 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "total_length" ) )) # Int |->_)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |-> ((Znth scan lens1 (0 : Int))))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ (((Znth scan lens1 (0 : Int)) + pivot_length) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth scan lens1 (0 : Int)) + pivot_length)) ”
)

noncomputable def quicksort_numbers_safety_wit_6_split_goal_1 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : (scan < high_pre)) (PreH2 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH3 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : ((0 : Int) <= low_pre)) (PreH9 : (low_pre < high_pre)) (PreH10 : (high_pre < count_pre)) (PreH11 : ((low_pre - 1) <= boundary)) (PreH12 : (boundary < scan)) (PreH13 : (low_pre <= scan)) (PreH14 : (scan <= high_pre)) (PreH15 : (1 <= (sum (lens)))) (PreH16 : ((sum (lens)) <= 200)) (PreH17 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH18 : (1 <= pivot_length)) (PreH19 : (pivot_length <= number_width_pre)) (PreH20 : ((Zlength (rows1)) = count_pre)) (PreH21 : ((Zlength (lens1)) = count_pre)) (PreH22 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH23 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH24 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH25 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH26 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH27 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH29 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "total_length" ) )) # Int |->_)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |-> ((Znth scan lens1 (0 : Int))))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ (((Znth scan lens1 (0 : Int)) + pivot_length) <= INT_MAX) ”

noncomputable def quicksort_numbers_safety_wit_6_split_goal_2 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : (scan < high_pre)) (PreH2 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH3 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : ((0 : Int) <= low_pre)) (PreH9 : (low_pre < high_pre)) (PreH10 : (high_pre < count_pre)) (PreH11 : ((low_pre - 1) <= boundary)) (PreH12 : (boundary < scan)) (PreH13 : (low_pre <= scan)) (PreH14 : (scan <= high_pre)) (PreH15 : (1 <= (sum (lens)))) (PreH16 : ((sum (lens)) <= 200)) (PreH17 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH18 : (1 <= pivot_length)) (PreH19 : (pivot_length <= number_width_pre)) (PreH20 : ((Zlength (rows1)) = count_pre)) (PreH21 : ((Zlength (lens1)) = count_pre)) (PreH22 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH23 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH24 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH25 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH26 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH27 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH29 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "total_length" ) )) # Int |->_)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |-> ((Znth scan lens1 (0 : Int))))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((INT_MIN) <= ((Znth scan lens1 (0 : Int)) + pivot_length)) ”

noncomputable def quicksort_numbers_safety_wit_7 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : (scan < high_pre)) (PreH2 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH3 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : ((0 : Int) <= low_pre)) (PreH9 : (low_pre < high_pre)) (PreH10 : (high_pre < count_pre)) (PreH11 : ((low_pre - 1) <= boundary)) (PreH12 : (boundary < scan)) (PreH13 : (low_pre <= scan)) (PreH14 : (scan <= high_pre)) (PreH15 : (1 <= (sum (lens)))) (PreH16 : ((sum (lens)) <= 200)) (PreH17 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH18 : (1 <= pivot_length)) (PreH19 : (pivot_length <= number_width_pre)) (PreH20 : ((Zlength (rows1)) = count_pre)) (PreH21 : ((Zlength (lens1)) = count_pre)) (PreH22 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH23 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH24 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH25 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH26 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH27 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH29 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "comparison" ) )) # Int |->_)
  ** ((( &( "total_length" ) )) # Int |-> (((Znth scan lens1 (0 : Int)) + pivot_length)))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |-> ((Znth scan lens1 (0 : Int))))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def quicksort_numbers_safety_wit_8 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : (scan < high_pre)) (PreH2 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH3 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : ((0 : Int) <= low_pre)) (PreH9 : (low_pre < high_pre)) (PreH10 : (high_pre < count_pre)) (PreH11 : ((low_pre - 1) <= boundary)) (PreH12 : (boundary < scan)) (PreH13 : (low_pre <= scan)) (PreH14 : (scan <= high_pre)) (PreH15 : (1 <= (sum (lens)))) (PreH16 : ((sum (lens)) <= 200)) (PreH17 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH18 : (1 <= pivot_length)) (PreH19 : (pivot_length <= number_width_pre)) (PreH20 : ((Zlength (rows1)) = count_pre)) (PreH21 : ((Zlength (lens1)) = count_pre)) (PreH22 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH23 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH24 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH25 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH26 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH27 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH29 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "position" ) )) # Int |->_)
  ** ((( &( "comparison" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "total_length" ) )) # Int |-> (((Znth scan lens1 (0 : Int)) + pivot_length)))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |-> ((Znth scan lens1 (0 : Int))))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def quicksort_numbers_safety_wit_9 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (position : Int) (comparison : Int) (total_length : Int) (current_length : Int) (lens1 : (List Int)) (pivot_length : Int) (boundary : Int) (scan : Int) (PreH1 : (position < current_length)) (PreH2 : (position < total_length)) (PreH3 : ((0 : Int) <= (scan * number_width_pre))) (PreH4 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH5 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH6 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH7 : (1 <= count_pre)) (PreH8 : (count_pre <= 20)) (PreH9 : (1 <= number_width_pre)) (PreH10 : (number_width_pre <= 10)) (PreH11 : ((0 : Int) <= low_pre)) (PreH12 : (low_pre < high_pre)) (PreH13 : (high_pre < count_pre)) (PreH14 : ((low_pre - 1) <= boundary)) (PreH15 : (boundary < scan)) (PreH16 : (low_pre <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (1 <= (sum (lens)))) (PreH19 : ((sum (lens)) <= 200)) (PreH20 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH21 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH22 : (1 <= current_length)) (PreH23 : (current_length <= number_width_pre)) (PreH24 : (1 <= pivot_length)) (PreH25 : (pivot_length <= number_width_pre)) (PreH26 : (total_length = (current_length + pivot_length))) (PreH27 : (comparison = (0 : Int))) (PreH28 : ((0 : Int) <= position)) (PreH29 : (position <= total_length)) (PreH30 : ((Zlength (rows1)) = count_pre)) (PreH31 : ((Zlength (lens1)) = count_pre)) (PreH32 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH34 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH35 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH36 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH38 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH39 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH40 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH41 : ((sum (lens1)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "right_digit" ) )) # Int |->_)
  ** ((( &( "left_digit" ) )) # Int |->_)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ (((scan * number_width_pre) + position) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((scan * number_width_pre) + position)) ”

noncomputable def quicksort_numbers_safety_wit_10 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (position : Int) (comparison : Int) (total_length : Int) (current_length : Int) (lens1 : (List Int)) (pivot_length : Int) (boundary : Int) (scan : Int) (PreH1 : (position < current_length)) (PreH2 : (position < total_length)) (PreH3 : ((0 : Int) <= (scan * number_width_pre))) (PreH4 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH5 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH6 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH7 : (1 <= count_pre)) (PreH8 : (count_pre <= 20)) (PreH9 : (1 <= number_width_pre)) (PreH10 : (number_width_pre <= 10)) (PreH11 : ((0 : Int) <= low_pre)) (PreH12 : (low_pre < high_pre)) (PreH13 : (high_pre < count_pre)) (PreH14 : ((low_pre - 1) <= boundary)) (PreH15 : (boundary < scan)) (PreH16 : (low_pre <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (1 <= (sum (lens)))) (PreH19 : ((sum (lens)) <= 200)) (PreH20 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH21 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH22 : (1 <= current_length)) (PreH23 : (current_length <= number_width_pre)) (PreH24 : (1 <= pivot_length)) (PreH25 : (pivot_length <= number_width_pre)) (PreH26 : (total_length = (current_length + pivot_length))) (PreH27 : (comparison = (0 : Int))) (PreH28 : ((0 : Int) <= position)) (PreH29 : (position <= total_length)) (PreH30 : ((Zlength (rows1)) = count_pre)) (PreH31 : ((Zlength (lens1)) = count_pre)) (PreH32 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH34 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH35 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH36 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH38 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH39 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH40 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH41 : ((sum (lens1)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "right_digit" ) )) # Int |->_)
  ** ((( &( "left_digit" ) )) # Int |->_)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((scan * number_width_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (scan * number_width_pre)) ”

noncomputable def quicksort_numbers_safety_wit_11 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (position : Int) (comparison : Int) (total_length : Int) (current_length : Int) (lens1 : (List Int)) (pivot_length : Int) (boundary : Int) (scan : Int) (PreH1 : (position >= current_length)) (PreH2 : (position < total_length)) (PreH3 : ((0 : Int) <= (scan * number_width_pre))) (PreH4 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH5 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH6 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH7 : (1 <= count_pre)) (PreH8 : (count_pre <= 20)) (PreH9 : (1 <= number_width_pre)) (PreH10 : (number_width_pre <= 10)) (PreH11 : ((0 : Int) <= low_pre)) (PreH12 : (low_pre < high_pre)) (PreH13 : (high_pre < count_pre)) (PreH14 : ((low_pre - 1) <= boundary)) (PreH15 : (boundary < scan)) (PreH16 : (low_pre <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (1 <= (sum (lens)))) (PreH19 : ((sum (lens)) <= 200)) (PreH20 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH21 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH22 : (1 <= current_length)) (PreH23 : (current_length <= number_width_pre)) (PreH24 : (1 <= pivot_length)) (PreH25 : (pivot_length <= number_width_pre)) (PreH26 : (total_length = (current_length + pivot_length))) (PreH27 : (comparison = (0 : Int))) (PreH28 : ((0 : Int) <= position)) (PreH29 : (position <= total_length)) (PreH30 : ((Zlength (rows1)) = count_pre)) (PreH31 : ((Zlength (lens1)) = count_pre)) (PreH32 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH34 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH35 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH36 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH38 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH39 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH40 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH41 : ((sum (lens1)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "right_digit" ) )) # Int |->_)
  ** ((( &( "left_digit" ) )) # Int |->_)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ (((high_pre * number_width_pre) + (position - current_length)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((high_pre * number_width_pre) + (position - current_length))) ”

noncomputable def quicksort_numbers_safety_wit_12 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (position : Int) (comparison : Int) (total_length : Int) (current_length : Int) (lens1 : (List Int)) (pivot_length : Int) (boundary : Int) (scan : Int) (PreH1 : (position >= current_length)) (PreH2 : (position < total_length)) (PreH3 : ((0 : Int) <= (scan * number_width_pre))) (PreH4 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH5 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH6 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH7 : (1 <= count_pre)) (PreH8 : (count_pre <= 20)) (PreH9 : (1 <= number_width_pre)) (PreH10 : (number_width_pre <= 10)) (PreH11 : ((0 : Int) <= low_pre)) (PreH12 : (low_pre < high_pre)) (PreH13 : (high_pre < count_pre)) (PreH14 : ((low_pre - 1) <= boundary)) (PreH15 : (boundary < scan)) (PreH16 : (low_pre <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (1 <= (sum (lens)))) (PreH19 : ((sum (lens)) <= 200)) (PreH20 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH21 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH22 : (1 <= current_length)) (PreH23 : (current_length <= number_width_pre)) (PreH24 : (1 <= pivot_length)) (PreH25 : (pivot_length <= number_width_pre)) (PreH26 : (total_length = (current_length + pivot_length))) (PreH27 : (comparison = (0 : Int))) (PreH28 : ((0 : Int) <= position)) (PreH29 : (position <= total_length)) (PreH30 : ((Zlength (rows1)) = count_pre)) (PreH31 : ((Zlength (lens1)) = count_pre)) (PreH32 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH34 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH35 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH36 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH38 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH39 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH40 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH41 : ((sum (lens1)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "right_digit" ) )) # Int |->_)
  ** ((( &( "left_digit" ) )) # Int |->_)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((position - current_length) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (position - current_length)) ”

noncomputable def quicksort_numbers_safety_wit_13 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (position : Int) (comparison : Int) (total_length : Int) (current_length : Int) (lens1 : (List Int)) (pivot_length : Int) (boundary : Int) (scan : Int) (PreH1 : (position >= current_length)) (PreH2 : (position < total_length)) (PreH3 : ((0 : Int) <= (scan * number_width_pre))) (PreH4 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH5 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH6 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH7 : (1 <= count_pre)) (PreH8 : (count_pre <= 20)) (PreH9 : (1 <= number_width_pre)) (PreH10 : (number_width_pre <= 10)) (PreH11 : ((0 : Int) <= low_pre)) (PreH12 : (low_pre < high_pre)) (PreH13 : (high_pre < count_pre)) (PreH14 : ((low_pre - 1) <= boundary)) (PreH15 : (boundary < scan)) (PreH16 : (low_pre <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (1 <= (sum (lens)))) (PreH19 : ((sum (lens)) <= 200)) (PreH20 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH21 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH22 : (1 <= current_length)) (PreH23 : (current_length <= number_width_pre)) (PreH24 : (1 <= pivot_length)) (PreH25 : (pivot_length <= number_width_pre)) (PreH26 : (total_length = (current_length + pivot_length))) (PreH27 : (comparison = (0 : Int))) (PreH28 : ((0 : Int) <= position)) (PreH29 : (position <= total_length)) (PreH30 : ((Zlength (rows1)) = count_pre)) (PreH31 : ((Zlength (lens1)) = count_pre)) (PreH32 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH34 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH35 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH36 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH38 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH39 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH40 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH41 : ((sum (lens1)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "right_digit" ) )) # Int |->_)
  ** ((( &( "left_digit" ) )) # Int |->_)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((high_pre * number_width_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (high_pre * number_width_pre)) ”

noncomputable def quicksort_numbers_safety_wit_14 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (scan : Int) (boundary : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (PreH1 : (position < pivot_length)) (PreH2 : ((0 : Int) <= (scan * number_width_pre))) (PreH3 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH20 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length))) (PreH26 : (comparison = (0 : Int))) (PreH27 : ((0 : Int) <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH30 : ((Zlength (rows1)) = count_pre)) (PreH31 : ((Zlength (lens1)) = count_pre)) (PreH32 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH34 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH35 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH36 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH38 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH39 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH40 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH41 : ((sum (lens1)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** ((( &( "left_digit" ) )) # Int |-> (left_digit))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "right_digit" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ (((high_pre * number_width_pre) + position) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((high_pre * number_width_pre) + position)) ”

noncomputable def quicksort_numbers_safety_wit_15 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (scan : Int) (boundary : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (PreH1 : (position < pivot_length)) (PreH2 : ((0 : Int) <= (scan * number_width_pre))) (PreH3 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH20 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length))) (PreH26 : (comparison = (0 : Int))) (PreH27 : ((0 : Int) <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH30 : ((Zlength (rows1)) = count_pre)) (PreH31 : ((Zlength (lens1)) = count_pre)) (PreH32 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH34 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH35 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH36 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH38 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH39 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH40 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH41 : ((sum (lens1)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** ((( &( "left_digit" ) )) # Int |-> (left_digit))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "right_digit" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((high_pre * number_width_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (high_pre * number_width_pre)) ”

noncomputable def quicksort_numbers_safety_wit_16 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (scan : Int) (boundary : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (PreH1 : (position >= pivot_length)) (PreH2 : ((0 : Int) <= (scan * number_width_pre))) (PreH3 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH20 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length))) (PreH26 : (comparison = (0 : Int))) (PreH27 : ((0 : Int) <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH30 : ((Zlength (rows1)) = count_pre)) (PreH31 : ((Zlength (lens1)) = count_pre)) (PreH32 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH34 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH35 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH36 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH38 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH39 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH40 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH41 : ((sum (lens1)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** ((( &( "left_digit" ) )) # Int |-> (left_digit))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "right_digit" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ (((scan * number_width_pre) + (position - pivot_length)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((scan * number_width_pre) + (position - pivot_length))) ”

noncomputable def quicksort_numbers_safety_wit_17 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (scan : Int) (boundary : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (PreH1 : (position >= pivot_length)) (PreH2 : ((0 : Int) <= (scan * number_width_pre))) (PreH3 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH20 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length))) (PreH26 : (comparison = (0 : Int))) (PreH27 : ((0 : Int) <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH30 : ((Zlength (rows1)) = count_pre)) (PreH31 : ((Zlength (lens1)) = count_pre)) (PreH32 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH34 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH35 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH36 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH38 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH39 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH40 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH41 : ((sum (lens1)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** ((( &( "left_digit" ) )) # Int |-> (left_digit))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "right_digit" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((position - pivot_length) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (position - pivot_length)) ”

noncomputable def quicksort_numbers_safety_wit_18 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (scan : Int) (boundary : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (PreH1 : (position >= pivot_length)) (PreH2 : ((0 : Int) <= (scan * number_width_pre))) (PreH3 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH20 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length))) (PreH26 : (comparison = (0 : Int))) (PreH27 : ((0 : Int) <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH30 : ((Zlength (rows1)) = count_pre)) (PreH31 : ((Zlength (lens1)) = count_pre)) (PreH32 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH34 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH35 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH36 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH38 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH39 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH40 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH41 : ((sum (lens1)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** ((( &( "left_digit" ) )) # Int |-> (left_digit))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "right_digit" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((scan * number_width_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (scan * number_width_pre)) ”

noncomputable def quicksort_numbers_safety_wit_19 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (scan : Int) (boundary : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (right_digit : Int) (PreH1 : (left_digit ≠ right_digit)) (PreH2 : ((0 : Int) <= (scan * number_width_pre))) (PreH3 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH20 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length))) (PreH26 : (comparison = (0 : Int))) (PreH27 : ((0 : Int) <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH30 : (right_digit = (ConcatRightDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH31 : ((Zlength (rows1)) = count_pre)) (PreH32 : ((Zlength (lens1)) = count_pre)) (PreH33 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH34 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH35 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH36 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH37 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH38 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH39 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH40 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH41 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH42 : ((sum (lens1)) = (sum (lens)))) (PreH43 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** ((( &( "left_digit" ) )) # Int |-> (left_digit))
  ** ((( &( "right_digit" ) )) # Int |-> (right_digit))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((left_digit - right_digit) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left_digit - right_digit)) ”
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (scan : Int) (boundary : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (right_digit : Int) (PreH1 : (left_digit ≠ right_digit)) (PreH2 : ((0 : Int) <= (scan * number_width_pre))) (PreH3 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH20 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length))) (PreH26 : (comparison = (0 : Int))) (PreH27 : ((0 : Int) <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH30 : (right_digit = (ConcatRightDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH31 : ((Zlength (rows1)) = count_pre)) (PreH32 : ((Zlength (lens1)) = count_pre)) (PreH33 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH34 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH35 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH36 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH37 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH38 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH39 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH40 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH41 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH42 : ((sum (lens1)) = (sum (lens)))) (PreH43 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** ((( &( "left_digit" ) )) # Int |-> (left_digit))
  ** ((( &( "right_digit" ) )) # Int |-> (right_digit))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((left_digit - right_digit) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left_digit - right_digit)) ”
)

noncomputable def quicksort_numbers_safety_wit_19_split_goal_1 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (scan : Int) (boundary : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (right_digit : Int) (PreH1 : (left_digit ≠ right_digit)) (PreH2 : ((0 : Int) <= (scan * number_width_pre))) (PreH3 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH20 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length))) (PreH26 : (comparison = (0 : Int))) (PreH27 : ((0 : Int) <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH30 : (right_digit = (ConcatRightDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH31 : ((Zlength (rows1)) = count_pre)) (PreH32 : ((Zlength (lens1)) = count_pre)) (PreH33 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH34 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH35 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH36 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH37 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH38 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH39 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH40 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH41 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH42 : ((sum (lens1)) = (sum (lens)))) (PreH43 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** ((( &( "left_digit" ) )) # Int |-> (left_digit))
  ** ((( &( "right_digit" ) )) # Int |-> (right_digit))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((left_digit - right_digit) <= INT_MAX) ”

noncomputable def quicksort_numbers_safety_wit_19_split_goal_2 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (scan : Int) (boundary : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (right_digit : Int) (PreH1 : (left_digit ≠ right_digit)) (PreH2 : ((0 : Int) <= (scan * number_width_pre))) (PreH3 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH20 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length))) (PreH26 : (comparison = (0 : Int))) (PreH27 : ((0 : Int) <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH30 : (right_digit = (ConcatRightDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH31 : ((Zlength (rows1)) = count_pre)) (PreH32 : ((Zlength (lens1)) = count_pre)) (PreH33 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH34 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH35 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH36 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH37 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH38 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH39 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH40 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH41 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH42 : ((sum (lens1)) = (sum (lens)))) (PreH43 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** ((( &( "left_digit" ) )) # Int |-> (left_digit))
  ** ((( &( "right_digit" ) )) # Int |-> (right_digit))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((INT_MIN) <= (left_digit - right_digit)) ”

noncomputable def quicksort_numbers_safety_wit_20 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (scan : Int) (boundary : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (right_digit : Int) (PreH1 : (left_digit = right_digit)) (PreH2 : ((0 : Int) <= (scan * number_width_pre))) (PreH3 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH20 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length))) (PreH26 : (comparison = (0 : Int))) (PreH27 : ((0 : Int) <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH30 : (right_digit = (ConcatRightDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH31 : ((Zlength (rows1)) = count_pre)) (PreH32 : ((Zlength (lens1)) = count_pre)) (PreH33 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH34 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH35 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH36 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH37 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH38 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH39 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH40 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH41 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH42 : ((sum (lens1)) = (sum (lens)))) (PreH43 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** ((( &( "position" ) )) # Int |-> (position))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((position + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (position + 1)) ”

noncomputable def quicksort_numbers_safety_wit_21 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (scan : Int) (boundary : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (PreH1 : ((0 : Int) <= (scan * number_width_pre))) (PreH2 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH3 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH4 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : ((0 : Int) <= low_pre)) (PreH10 : (low_pre < high_pre)) (PreH11 : (high_pre < count_pre)) (PreH12 : ((low_pre - 1) <= boundary)) (PreH13 : (boundary < scan)) (PreH14 : (low_pre <= scan)) (PreH15 : (scan < high_pre)) (PreH16 : (1 <= (sum (lens)))) (PreH17 : ((sum (lens)) <= 200)) (PreH18 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH19 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH20 : (1 <= current_length)) (PreH21 : (current_length <= number_width_pre)) (PreH22 : (1 <= pivot_length)) (PreH23 : (pivot_length <= number_width_pre)) (PreH24 : (total_length = (current_length + pivot_length))) (PreH25 : ((Zlength (rows1)) = count_pre)) (PreH26 : ((Zlength (lens1)) = count_pre)) (PreH27 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH28 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH29 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH31 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH32 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH33 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH34 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH35 : (ConcatCompareOutcome rows1 lens1 scan high_pre comparison)) (PreH36 : ((sum (lens1)) = (sum (lens)))) (PreH37 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "position" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def quicksort_numbers_safety_wit_22 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (scan : Int) (boundary : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (PreH1 : (comparison > (0 : Int))) (PreH2 : ((0 : Int) <= (scan * number_width_pre))) (PreH3 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH20 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length))) (PreH26 : ((Zlength (rows1)) = count_pre)) (PreH27 : ((Zlength (lens1)) = count_pre)) (PreH28 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH29 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH30 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH31 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH32 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH33 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH34 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH35 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH36 : (ConcatCompareOutcome rows1 lens1 scan high_pre comparison)) (PreH37 : ((sum (lens1)) = (sum (lens)))) (PreH38 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "temporary_length" ) )) # Int |->_)
  ** ((( &( "column" ) )) # Int |->_)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "position" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((boundary + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (boundary + 1)) ”

noncomputable def quicksort_numbers_safety_wit_23 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (scan : Int) (boundary : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (PreH1 : (comparison > (0 : Int))) (PreH2 : ((0 : Int) <= (scan * number_width_pre))) (PreH3 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH20 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length))) (PreH26 : ((Zlength (rows1)) = count_pre)) (PreH27 : ((Zlength (lens1)) = count_pre)) (PreH28 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH29 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH30 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH31 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH32 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH33 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH34 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH35 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH36 : (ConcatCompareOutcome rows1 lens1 scan high_pre comparison)) (PreH37 : ((sum (lens1)) = (sum (lens)))) (PreH38 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "temporary_length" ) )) # Int |->_)
  ** ((( &( "column" ) )) # Int |->_)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "boundary" ) )) # Int |-> ((boundary + 1)))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "position" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def quicksort_numbers_safety_wit_24 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : (column < number_width_pre)) (PreH2 : ((0 : Int) <= (boundary * number_width_pre))) (PreH3 : (((boundary * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (scan * number_width_pre))) (PreH5 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH7 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : ((0 : Int) <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : ((0 : Int) <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1)) = count_pre)) (PreH27 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before)))) (PreH28 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH29 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH31 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH32 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1)))) (PreH33 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1)))) (PreH34 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH35 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH36 : (comparison > (0 : Int))) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH38 : ((sum (lens1)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  ((( &( "temporary_digit" ) )) # Int |->_)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |->_)
  ** ((( &( "total_length" ) )) # Int |->_)
  ** ((( &( "position" ) )) # Int |->_)
  ** ((( &( "temporary_length" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ (((boundary * number_width_pre) + column) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((boundary * number_width_pre) + column)) ”

noncomputable def quicksort_numbers_safety_wit_25 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : (column < number_width_pre)) (PreH2 : ((0 : Int) <= (boundary * number_width_pre))) (PreH3 : (((boundary * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (scan * number_width_pre))) (PreH5 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH7 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : ((0 : Int) <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : ((0 : Int) <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1)) = count_pre)) (PreH27 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before)))) (PreH28 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH29 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH31 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH32 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1)))) (PreH33 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1)))) (PreH34 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH35 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH36 : (comparison > (0 : Int))) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH38 : ((sum (lens1)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  ((( &( "temporary_digit" ) )) # Int |->_)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |->_)
  ** ((( &( "total_length" ) )) # Int |->_)
  ** ((( &( "position" ) )) # Int |->_)
  ** ((( &( "temporary_length" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((boundary * number_width_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (boundary * number_width_pre)) ”

noncomputable def quicksort_numbers_safety_wit_26 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : (column < number_width_pre)) (PreH2 : ((0 : Int) <= (boundary * number_width_pre))) (PreH3 : (((boundary * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (scan * number_width_pre))) (PreH5 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH7 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : ((0 : Int) <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : ((0 : Int) <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1)) = count_pre)) (PreH27 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before)))) (PreH28 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH29 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH31 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH32 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1)))) (PreH33 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1)))) (PreH34 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH35 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH36 : (comparison > (0 : Int))) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH38 : ((sum (lens1)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** ((( &( "temporary_digit" ) )) # Int |-> ((Znth ((boundary * number_width_pre) + column) flat_now (0 : Int))))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |->_)
  ** ((( &( "total_length" ) )) # Int |->_)
  ** ((( &( "position" ) )) # Int |->_)
  ** ((( &( "temporary_length" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ (((boundary * number_width_pre) + column) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((boundary * number_width_pre) + column)) ”

noncomputable def quicksort_numbers_safety_wit_27 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : (column < number_width_pre)) (PreH2 : ((0 : Int) <= (boundary * number_width_pre))) (PreH3 : (((boundary * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (scan * number_width_pre))) (PreH5 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH7 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : ((0 : Int) <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : ((0 : Int) <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1)) = count_pre)) (PreH27 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before)))) (PreH28 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH29 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH31 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH32 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1)))) (PreH33 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1)))) (PreH34 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH35 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH36 : (comparison > (0 : Int))) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH38 : ((sum (lens1)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** ((( &( "temporary_digit" ) )) # Int |-> ((Znth ((boundary * number_width_pre) + column) flat_now (0 : Int))))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |->_)
  ** ((( &( "total_length" ) )) # Int |->_)
  ** ((( &( "position" ) )) # Int |->_)
  ** ((( &( "temporary_length" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((boundary * number_width_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (boundary * number_width_pre)) ”

noncomputable def quicksort_numbers_safety_wit_28 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : (column < number_width_pre)) (PreH2 : ((0 : Int) <= (boundary * number_width_pre))) (PreH3 : (((boundary * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (scan * number_width_pre))) (PreH5 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH7 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : ((0 : Int) <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : ((0 : Int) <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1)) = count_pre)) (PreH27 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before)))) (PreH28 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH29 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH31 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH32 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1)))) (PreH33 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1)))) (PreH34 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH35 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH36 : (comparison > (0 : Int))) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH38 : ((sum (lens1)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** ((( &( "temporary_digit" ) )) # Int |-> ((Znth ((boundary * number_width_pre) + column) flat_now (0 : Int))))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |->_)
  ** ((( &( "total_length" ) )) # Int |->_)
  ** ((( &( "position" ) )) # Int |->_)
  ** ((( &( "temporary_length" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ (((scan * number_width_pre) + column) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((scan * number_width_pre) + column)) ”

noncomputable def quicksort_numbers_safety_wit_29 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : (column < number_width_pre)) (PreH2 : ((0 : Int) <= (boundary * number_width_pre))) (PreH3 : (((boundary * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (scan * number_width_pre))) (PreH5 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH7 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : ((0 : Int) <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : ((0 : Int) <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1)) = count_pre)) (PreH27 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before)))) (PreH28 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH29 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH31 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH32 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1)))) (PreH33 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1)))) (PreH34 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH35 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH36 : (comparison > (0 : Int))) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH38 : ((sum (lens1)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** ((( &( "temporary_digit" ) )) # Int |-> ((Znth ((boundary * number_width_pre) + column) flat_now (0 : Int))))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |->_)
  ** ((( &( "total_length" ) )) # Int |->_)
  ** ((( &( "position" ) )) # Int |->_)
  ** ((( &( "temporary_length" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((scan * number_width_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (scan * number_width_pre)) ”

noncomputable def quicksort_numbers_safety_wit_30 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : (column < number_width_pre)) (PreH2 : ((0 : Int) <= (boundary * number_width_pre))) (PreH3 : (((boundary * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (scan * number_width_pre))) (PreH5 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH7 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : ((0 : Int) <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : ((0 : Int) <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1)) = count_pre)) (PreH27 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before)))) (PreH28 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH29 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH31 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH32 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1)))) (PreH33 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1)))) (PreH34 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH35 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH36 : (comparison > (0 : Int))) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH38 : ((sum (lens1)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) (replace_Znth (((boundary * number_width_pre) + column)) ((Znth ((scan * number_width_pre) + column) flat_now (0 : Int))) (flat_now)))
  ** ((( &( "temporary_digit" ) )) # Int |-> ((Znth ((boundary * number_width_pre) + column) flat_now (0 : Int))))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |->_)
  ** ((( &( "total_length" ) )) # Int |->_)
  ** ((( &( "position" ) )) # Int |->_)
  ** ((( &( "temporary_length" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ (((scan * number_width_pre) + column) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((scan * number_width_pre) + column)) ”

noncomputable def quicksort_numbers_safety_wit_31 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : (column < number_width_pre)) (PreH2 : ((0 : Int) <= (boundary * number_width_pre))) (PreH3 : (((boundary * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (scan * number_width_pre))) (PreH5 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH7 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : ((0 : Int) <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : ((0 : Int) <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1)) = count_pre)) (PreH27 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before)))) (PreH28 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH29 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH31 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH32 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1)))) (PreH33 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1)))) (PreH34 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH35 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH36 : (comparison > (0 : Int))) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH38 : ((sum (lens1)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) (replace_Znth (((boundary * number_width_pre) + column)) ((Znth ((scan * number_width_pre) + column) flat_now (0 : Int))) (flat_now)))
  ** ((( &( "temporary_digit" ) )) # Int |-> ((Znth ((boundary * number_width_pre) + column) flat_now (0 : Int))))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |->_)
  ** ((( &( "total_length" ) )) # Int |->_)
  ** ((( &( "position" ) )) # Int |->_)
  ** ((( &( "temporary_length" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((scan * number_width_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (scan * number_width_pre)) ”

noncomputable def quicksort_numbers_safety_wit_32 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : (column < number_width_pre)) (PreH2 : ((0 : Int) <= (boundary * number_width_pre))) (PreH3 : (((boundary * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (scan * number_width_pre))) (PreH5 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH7 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : ((0 : Int) <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : ((0 : Int) <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1)) = count_pre)) (PreH27 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before)))) (PreH28 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH29 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH31 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH32 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1)))) (PreH33 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1)))) (PreH34 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH35 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH36 : (comparison > (0 : Int))) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH38 : ((sum (lens1)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) (replace_Znth (((scan * number_width_pre) + column)) ((Znth ((boundary * number_width_pre) + column) flat_now (0 : Int))) ((replace_Znth (((boundary * number_width_pre) + column)) ((Znth ((scan * number_width_pre) + column) flat_now (0 : Int))) (flat_now)))))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |->_)
  ** ((( &( "total_length" ) )) # Int |->_)
  ** ((( &( "position" ) )) # Int |->_)
  ** ((( &( "temporary_length" ) )) # Int |->_)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((column + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (column + 1)) ”

noncomputable def quicksort_numbers_safety_wit_33 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (PreH1 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH2 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : ((0 : Int) <= low_pre)) (PreH8 : (low_pre < high_pre)) (PreH9 : (high_pre < count_pre)) (PreH10 : ((low_pre - 1) <= boundary)) (PreH11 : (boundary <= scan)) (PreH12 : (scan < high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH16 : (1 <= pivot_length)) (PreH17 : (pivot_length <= number_width_pre)) (PreH18 : ((Zlength (rows1)) = count_pre)) (PreH19 : ((Zlength (lens1)) = count_pre)) (PreH20 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH21 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH22 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH23 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH24 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH26 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH27 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary (scan + 1))) (PreH28 : ((sum (lens1)) = (sum (lens)))) (PreH29 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((scan + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (scan + 1)) ”

noncomputable def quicksort_numbers_safety_wit_34 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : (scan >= high_pre)) (PreH2 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH3 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : ((0 : Int) <= low_pre)) (PreH9 : (low_pre < high_pre)) (PreH10 : (high_pre < count_pre)) (PreH11 : ((low_pre - 1) <= boundary)) (PreH12 : (boundary < scan)) (PreH13 : (low_pre <= scan)) (PreH14 : (scan <= high_pre)) (PreH15 : (1 <= (sum (lens)))) (PreH16 : ((sum (lens)) <= 200)) (PreH17 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH18 : (1 <= pivot_length)) (PreH19 : (pivot_length <= number_width_pre)) (PreH20 : ((Zlength (rows1)) = count_pre)) (PreH21 : ((Zlength (lens1)) = count_pre)) (PreH22 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH23 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH24 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH25 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH26 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH27 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH29 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ ((boundary + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (boundary + 1)) ”

noncomputable def quicksort_numbers_safety_wit_35 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : (scan >= high_pre)) (PreH2 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH3 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : ((0 : Int) <= low_pre)) (PreH9 : (low_pre < high_pre)) (PreH10 : (high_pre < count_pre)) (PreH11 : ((low_pre - 1) <= boundary)) (PreH12 : (boundary < scan)) (PreH13 : (low_pre <= scan)) (PreH14 : (scan <= high_pre)) (PreH15 : (1 <= (sum (lens)))) (PreH16 : ((sum (lens)) <= 200)) (PreH17 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH18 : (1 <= pivot_length)) (PreH19 : (pivot_length <= number_width_pre)) (PreH20 : ((Zlength (rows1)) = count_pre)) (PreH21 : ((Zlength (lens1)) = count_pre)) (PreH22 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH23 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH24 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH25 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH26 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH27 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH29 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot" ) )) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def quicksort_numbers_safety_wit_36 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : (scan >= high_pre)) (PreH2 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH3 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : ((0 : Int) <= low_pre)) (PreH9 : (low_pre < high_pre)) (PreH10 : (high_pre < count_pre)) (PreH11 : ((low_pre - 1) <= boundary)) (PreH12 : (boundary < scan)) (PreH13 : (low_pre <= scan)) (PreH14 : (scan <= high_pre)) (PreH15 : (1 <= (sum (lens)))) (PreH16 : ((sum (lens)) <= 200)) (PreH17 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH18 : (1 <= pivot_length)) (PreH19 : (pivot_length <= number_width_pre)) (PreH20 : ((Zlength (rows1)) = count_pre)) (PreH21 : ((Zlength (lens1)) = count_pre)) (PreH22 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH23 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH24 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH25 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH26 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH27 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH29 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "column" ) )) # Int |->_)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot" ) )) # Int |-> ((boundary + 1)))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def quicksort_numbers_safety_wit_37 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : (column < number_width_pre)) (PreH2 : ((0 : Int) <= (pivot * number_width_pre))) (PreH3 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : ((0 : Int) <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before)))) (PreH25 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH26 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH27 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1)))) (PreH30 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1)))) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  ((( &( "temporary_digit" ) )) # Int |->_)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
|--
  “ (((pivot * number_width_pre) + column) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((pivot * number_width_pre) + column)) ”

noncomputable def quicksort_numbers_safety_wit_38 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : (column < number_width_pre)) (PreH2 : ((0 : Int) <= (pivot * number_width_pre))) (PreH3 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : ((0 : Int) <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before)))) (PreH25 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH26 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH27 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1)))) (PreH30 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1)))) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  ((( &( "temporary_digit" ) )) # Int |->_)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
|--
  “ ((pivot * number_width_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (pivot * number_width_pre)) ”

noncomputable def quicksort_numbers_safety_wit_39 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : (column < number_width_pre)) (PreH2 : ((0 : Int) <= (pivot * number_width_pre))) (PreH3 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : ((0 : Int) <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before)))) (PreH25 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH26 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH27 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1)))) (PreH30 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1)))) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** ((( &( "temporary_digit" ) )) # Int |-> ((Znth ((pivot * number_width_pre) + column) flat_now (0 : Int))))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
|--
  “ (((pivot * number_width_pre) + column) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((pivot * number_width_pre) + column)) ”

noncomputable def quicksort_numbers_safety_wit_40 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : (column < number_width_pre)) (PreH2 : ((0 : Int) <= (pivot * number_width_pre))) (PreH3 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : ((0 : Int) <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before)))) (PreH25 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH26 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH27 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1)))) (PreH30 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1)))) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** ((( &( "temporary_digit" ) )) # Int |-> ((Znth ((pivot * number_width_pre) + column) flat_now (0 : Int))))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
|--
  “ ((pivot * number_width_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (pivot * number_width_pre)) ”

noncomputable def quicksort_numbers_safety_wit_41 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : (column < number_width_pre)) (PreH2 : ((0 : Int) <= (pivot * number_width_pre))) (PreH3 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : ((0 : Int) <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before)))) (PreH25 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH26 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH27 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1)))) (PreH30 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1)))) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** ((( &( "temporary_digit" ) )) # Int |-> ((Znth ((pivot * number_width_pre) + column) flat_now (0 : Int))))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
|--
  “ (((high_pre * number_width_pre) + column) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((high_pre * number_width_pre) + column)) ”

noncomputable def quicksort_numbers_safety_wit_42 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : (column < number_width_pre)) (PreH2 : ((0 : Int) <= (pivot * number_width_pre))) (PreH3 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : ((0 : Int) <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before)))) (PreH25 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH26 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH27 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1)))) (PreH30 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1)))) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** ((( &( "temporary_digit" ) )) # Int |-> ((Znth ((pivot * number_width_pre) + column) flat_now (0 : Int))))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
|--
  “ ((high_pre * number_width_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (high_pre * number_width_pre)) ”

noncomputable def quicksort_numbers_safety_wit_43 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : (column < number_width_pre)) (PreH2 : ((0 : Int) <= (pivot * number_width_pre))) (PreH3 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : ((0 : Int) <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before)))) (PreH25 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH26 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH27 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1)))) (PreH30 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1)))) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) (replace_Znth (((pivot * number_width_pre) + column)) ((Znth ((high_pre * number_width_pre) + column) flat_now (0 : Int))) (flat_now)))
  ** ((( &( "temporary_digit" ) )) # Int |-> ((Znth ((pivot * number_width_pre) + column) flat_now (0 : Int))))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
|--
  “ (((high_pre * number_width_pre) + column) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((high_pre * number_width_pre) + column)) ”

noncomputable def quicksort_numbers_safety_wit_44 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : (column < number_width_pre)) (PreH2 : ((0 : Int) <= (pivot * number_width_pre))) (PreH3 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : ((0 : Int) <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before)))) (PreH25 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH26 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH27 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1)))) (PreH30 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1)))) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) (replace_Znth (((pivot * number_width_pre) + column)) ((Znth ((high_pre * number_width_pre) + column) flat_now (0 : Int))) (flat_now)))
  ** ((( &( "temporary_digit" ) )) # Int |-> ((Znth ((pivot * number_width_pre) + column) flat_now (0 : Int))))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
|--
  “ ((high_pre * number_width_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (high_pre * number_width_pre)) ”

noncomputable def quicksort_numbers_safety_wit_45 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : (column < number_width_pre)) (PreH2 : ((0 : Int) <= (pivot * number_width_pre))) (PreH3 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : ((0 : Int) <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before)))) (PreH25 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH26 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH27 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1)))) (PreH30 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1)))) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) (replace_Znth (((high_pre * number_width_pre) + column)) ((Znth ((pivot * number_width_pre) + column) flat_now (0 : Int))) ((replace_Znth (((pivot * number_width_pre) + column)) ((Znth ((high_pre * number_width_pre) + column) flat_now (0 : Int))) (flat_now)))))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "column" ) )) # Int |-> (column))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
|--
  “ ((column + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (column + 1)) ”

noncomputable def quicksort_numbers_safety_wit_46 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (PreH1 : (pivot > low_pre)) (PreH2 : ((0 : Int) <= (pivot * number_width_pre))) (PreH3 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : (1 <= (sum (lens)))) (PreH16 : ((sum (lens)) <= 200)) (PreH17 : ((Zlength (rows1)) = count_pre)) (PreH18 : ((Zlength (lens1)) = count_pre)) (PreH19 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH20 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH21 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH23 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH24 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH25 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH26 : (PairedPermutation rows rows1 lens lens1)) (PreH27 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH28 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH29 : ((sum (lens1)) = (sum (lens)))) (PreH30 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
  ** ((( &( "pivot_length" ) )) # Int |->_)
|--
  “ ((pivot - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (pivot - 1)) ”

noncomputable def quicksort_numbers_safety_wit_47 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (PreH1 : (pivot > low_pre)) (PreH2 : ((0 : Int) <= (pivot * number_width_pre))) (PreH3 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : (1 <= (sum (lens)))) (PreH16 : ((sum (lens)) <= 200)) (PreH17 : ((Zlength (rows1)) = count_pre)) (PreH18 : ((Zlength (lens1)) = count_pre)) (PreH19 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH20 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH21 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH23 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH24 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH25 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH26 : (PairedPermutation rows rows1 lens lens1)) (PreH27 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH28 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH29 : ((sum (lens1)) = (sum (lens)))) (PreH30 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
  ** ((( &( "pivot_length" ) )) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def quicksort_numbers_safety_wit_48 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (rows2 : (List (List Int))) (lens2 : (List Int)) (flat2 : (List Int)) (PreH1 : (pivot < high_pre)) (PreH2 : (FlatRows flat2 rows2 count_pre number_width_pre)) (PreH3 : (PairedPermutation rows1 rows2 lens1 lens2)) (PreH4 : (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1))) (PreH5 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1))) (PreH6 : (pivot > low_pre)) (PreH7 : ((0 : Int) <= (pivot * number_width_pre))) (PreH8 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH9 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH10 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH11 : (1 <= count_pre)) (PreH12 : (count_pre <= 20)) (PreH13 : (1 <= number_width_pre)) (PreH14 : (number_width_pre <= 10)) (PreH15 : ((0 : Int) <= low_pre)) (PreH16 : (low_pre < high_pre)) (PreH17 : (high_pre < count_pre)) (PreH18 : (low_pre <= pivot)) (PreH19 : (pivot <= high_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : ((Zlength (rows1)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH25 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH26 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH27 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH30 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH31 : (PairedPermutation rows rows1 lens lens1)) (PreH32 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH33 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH34 : ((sum (lens1)) = (sum (lens)))) (PreH35 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat2)
  ** (intArray.full lengths_pre count_pre lens2)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
  ** ((( &( "pivot_length" ) )) # Int |->_)
|--
  “ ((pivot + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (pivot + 1)) ”

noncomputable def quicksort_numbers_safety_wit_49 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (rows2 : (List (List Int))) (lens2 : (List Int)) (flat2 : (List Int)) (PreH1 : (pivot < high_pre)) (PreH2 : (FlatRows flat2 rows2 count_pre number_width_pre)) (PreH3 : (PairedPermutation rows1 rows2 lens1 lens2)) (PreH4 : (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1))) (PreH5 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1))) (PreH6 : (pivot > low_pre)) (PreH7 : ((0 : Int) <= (pivot * number_width_pre))) (PreH8 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH9 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH10 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH11 : (1 <= count_pre)) (PreH12 : (count_pre <= 20)) (PreH13 : (1 <= number_width_pre)) (PreH14 : (number_width_pre <= 10)) (PreH15 : ((0 : Int) <= low_pre)) (PreH16 : (low_pre < high_pre)) (PreH17 : (high_pre < count_pre)) (PreH18 : (low_pre <= pivot)) (PreH19 : (pivot <= high_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : ((Zlength (rows1)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH25 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH26 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH27 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH30 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH31 : (PairedPermutation rows rows1 lens lens1)) (PreH32 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH33 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH34 : ((sum (lens1)) = (sum (lens)))) (PreH35 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat2)
  ** (intArray.full lengths_pre count_pre lens2)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
  ** ((( &( "pivot_length" ) )) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def quicksort_numbers_safety_wit_50 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (PreH1 : (pivot >= high_pre)) (PreH2 : (pivot <= low_pre)) (PreH3 : ((0 : Int) <= (pivot * number_width_pre))) (PreH4 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH5 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH6 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH7 : (1 <= count_pre)) (PreH8 : (count_pre <= 20)) (PreH9 : (1 <= number_width_pre)) (PreH10 : (number_width_pre <= 10)) (PreH11 : ((0 : Int) <= low_pre)) (PreH12 : (low_pre < high_pre)) (PreH13 : (high_pre < count_pre)) (PreH14 : (low_pre <= pivot)) (PreH15 : (pivot <= high_pre)) (PreH16 : (1 <= (sum (lens)))) (PreH17 : ((sum (lens)) <= 200)) (PreH18 : ((Zlength (rows1)) = count_pre)) (PreH19 : ((Zlength (lens1)) = count_pre)) (PreH20 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH21 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH22 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH23 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH24 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH26 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH27 : (PairedPermutation rows rows1 lens lens1)) (PreH28 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH29 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
  ** ((( &( "pivot_length" ) )) # Int |->_)
|--
  “ False ”

noncomputable def quicksort_numbers_safety_wit_51 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (PreH1 : (pivot < high_pre)) (PreH2 : (pivot <= low_pre)) (PreH3 : ((0 : Int) <= (pivot * number_width_pre))) (PreH4 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH5 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH6 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH7 : (1 <= count_pre)) (PreH8 : (count_pre <= 20)) (PreH9 : (1 <= number_width_pre)) (PreH10 : (number_width_pre <= 10)) (PreH11 : ((0 : Int) <= low_pre)) (PreH12 : (low_pre < high_pre)) (PreH13 : (high_pre < count_pre)) (PreH14 : (low_pre <= pivot)) (PreH15 : (pivot <= high_pre)) (PreH16 : (1 <= (sum (lens)))) (PreH17 : ((sum (lens)) <= 200)) (PreH18 : ((Zlength (rows1)) = count_pre)) (PreH19 : ((Zlength (lens1)) = count_pre)) (PreH20 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH21 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH22 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH23 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH24 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH26 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH27 : (PairedPermutation rows rows1 lens lens1)) (PreH28 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH29 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
  ** ((( &( "pivot_length" ) )) # Int |->_)
|--
  “ ((pivot + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (pivot + 1)) ”

noncomputable def quicksort_numbers_safety_wit_52 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (PreH1 : (pivot < high_pre)) (PreH2 : (pivot <= low_pre)) (PreH3 : ((0 : Int) <= (pivot * number_width_pre))) (PreH4 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH5 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH6 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH7 : (1 <= count_pre)) (PreH8 : (count_pre <= 20)) (PreH9 : (1 <= number_width_pre)) (PreH10 : (number_width_pre <= 10)) (PreH11 : ((0 : Int) <= low_pre)) (PreH12 : (low_pre < high_pre)) (PreH13 : (high_pre < count_pre)) (PreH14 : (low_pre <= pivot)) (PreH15 : (pivot <= high_pre)) (PreH16 : (1 <= (sum (lens)))) (PreH17 : ((sum (lens)) <= 200)) (PreH18 : ((Zlength (rows1)) = count_pre)) (PreH19 : ((Zlength (lens1)) = count_pre)) (PreH20 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH21 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH22 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH23 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH24 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH26 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH27 : (PairedPermutation rows rows1 lens lens1)) (PreH28 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH29 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
  ** ((( &( "pivot_length" ) )) # Int |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def quicksort_numbers_entail_wit_1 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (high_pre < count_pre)) (PreH2 : (low_pre < high_pre)) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : ((0 : Int) <= low_pre)) (PreH9 : (low_pre <= count_pre)) (PreH10 : ((-1) <= high_pre)) (PreH11 : (high_pre < count_pre)) (PreH12 : (1 <= (sum (lens)))) (PreH13 : ((sum (lens)) <= 200)) (PreH14 : ((Zlength (rows)) = count_pre)) (PreH15 : ((Zlength (lens)) = count_pre)) (PreH16 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows)))) (PreH17 : (Forall ((LE.le (α := Int)) (1)) lens)) (PreH18 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens)) (PreH19 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH20 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows) (lens)))) (PreH22 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows) (lens)))) (PreH23 : (FlatRows flat rows count_pre number_width_pre)) ,
  (intArray.full lengths_pre count_pre lens)
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat)
|--
  EX flat1 : (List Int), EX rows1 : (List (List Int)), EX lens1 : (List Int),
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= (low_pre - 1)) ” &&
  “ ((low_pre - 1) < low_pre) ” &&
  “ (low_pre <= low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ ((Znth high_pre lens (0 : Int)) = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= (Znth high_pre lens (0 : Int))) ” &&
  “ ((Znth high_pre lens (0 : Int)) <= number_width_pre) ” &&
  “ ((Zlength (rows1)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1))) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre (low_pre - 1) low_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (high_pre < count_pre)) (PreH2 : (low_pre < high_pre)) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : ((0 : Int) <= low_pre)) (PreH9 : (low_pre <= count_pre)) (PreH10 : ((-1) <= high_pre)) (PreH11 : (high_pre < count_pre)) (PreH12 : (1 <= (sum (lens)))) (PreH13 : ((sum (lens)) <= 200)) (PreH14 : ((Zlength (rows)) = count_pre)) (PreH15 : ((Zlength (lens)) = count_pre)) (PreH16 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows)))) (PreH17 : (Forall ((LE.le (α := Int)) (1)) lens)) (PreH18 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens)) (PreH19 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH20 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows) (lens)))) (PreH22 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows) (lens)))) (PreH23 : (FlatRows flat rows count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= ((Zlength (rows)) * number_width_pre)) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (high_pre < (Zlength (rows))) ” &&
  “ ((low_pre - 1) <= (low_pre - 1)) ” &&
  “ ((low_pre - 1) < low_pre) ” &&
  “ (low_pre <= low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ ((Znth high_pre lens (0 : Int)) = (Znth (high_pre) (lens) ((0 : Int)))) ” &&
  “ (1 <= (Znth high_pre lens (0 : Int))) ” &&
  “ ((Znth high_pre lens (0 : Int)) <= number_width_pre) ” &&
  “ ((Zlength (rows1)) = (Zlength (rows))) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens))) ” &&
  “ (PartitionScanState rows rows1 lens lens low_pre high_pre (low_pre - 1) low_pre) ” &&
  “ (FlatRows flat rows1 (Zlength (rows)) number_width_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_2 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1_2 : (List Int)) (rows1_2 : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : (scan < high_pre)) (PreH2 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH3 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : ((0 : Int) <= low_pre)) (PreH9 : (low_pre < high_pre)) (PreH10 : (high_pre < count_pre)) (PreH11 : ((low_pre - 1) <= boundary)) (PreH12 : (boundary < scan)) (PreH13 : (low_pre <= scan)) (PreH14 : (scan <= high_pre)) (PreH15 : (1 <= (sum (lens)))) (PreH16 : ((sum (lens)) <= 200)) (PreH17 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH18 : (1 <= pivot_length)) (PreH19 : (pivot_length <= number_width_pre)) (PreH20 : ((Zlength (rows1_2)) = count_pre)) (PreH21 : ((Zlength (lens1)) = count_pre)) (PreH22 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1_2)))) (PreH23 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH24 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH25 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH26 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH27 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1_2) (lens1)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1_2) (lens1)))) (PreH29 : (PartitionScanState rows rows1_2 lens lens1 low_pre high_pre boundary scan)) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  (intArray.full lengths_pre count_pre lens1)
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1_2)
|--
  EX flat1 : (List Int), EX rows1 : (List (List Int)), EX lens1_2 : (List Int),
  “ ((0 : Int) <= (scan * number_width_pre)) ” &&
  “ (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary < scan) ” &&
  “ (low_pre <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int)))) ” &&
  “ ((Znth scan lens1 (0 : Int)) = (Znth (scan) (lens1_2) ((0 : Int)))) ” &&
  “ (1 <= (Znth scan lens1 (0 : Int))) ” &&
  “ ((Znth scan lens1 (0 : Int)) <= number_width_pre) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (((Znth scan lens1 (0 : Int)) + pivot_length) = ((Znth scan lens1 (0 : Int)) + pivot_length)) ” &&
  “ ((0 : Int) = (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= ((Znth scan lens1 (0 : Int)) + pivot_length)) ” &&
  “ ((Zlength (rows1)) = count_pre) ” &&
  “ ((Zlength (lens1_2)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1_2) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1_2))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1_2))) ” &&
  “ (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1_2 scan high_pre (0 : Int)) ” &&
  “ ((sum (lens1_2)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1_2)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1_2 : (List Int)) (rows1_2 : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : (scan < high_pre)) (PreH2 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH3 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : ((0 : Int) <= low_pre)) (PreH9 : (low_pre < high_pre)) (PreH10 : (high_pre < count_pre)) (PreH11 : ((low_pre - 1) <= boundary)) (PreH12 : (boundary < scan)) (PreH13 : (low_pre <= scan)) (PreH14 : (scan <= high_pre)) (PreH15 : (1 <= (sum (lens)))) (PreH16 : ((sum (lens)) <= 200)) (PreH17 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH18 : (1 <= pivot_length)) (PreH19 : (pivot_length <= number_width_pre)) (PreH20 : ((Zlength (rows1_2)) = count_pre)) (PreH21 : ((Zlength (lens1)) = count_pre)) (PreH22 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1_2)))) (PreH23 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH24 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH25 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH26 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH27 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1_2) (lens1)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1_2) (lens1)))) (PreH29 : (PartitionScanState rows rows1_2 lens lens1 low_pre high_pre boundary scan)) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ ((0 : Int) <= (scan * number_width_pre)) ” &&
  “ (((scan * number_width_pre) + number_width_pre) <= ((Zlength (rows1_2)) * number_width_pre)) ” &&
  “ ((Znth scan lens1 (0 : Int)) = (Znth (scan) (lens1) ((0 : Int)))) ” &&
  “ (1 <= (Znth scan lens1 (0 : Int))) ” &&
  “ ((Znth scan lens1 (0 : Int)) <= number_width_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= ((Znth scan lens1 (0 : Int)) + (Znth (high_pre) (lens1) ((0 : Int))))) ” &&
  “ ((Zlength (rows1)) = (Zlength (rows1_2))) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1))) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1 scan high_pre (0 : Int)) ” &&
  “ (FlatRows flat1_2 rows1 (Zlength (rows1_2)) number_width_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_3_1 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1_2 : (List (List Int))) (position : Int) (comparison : Int) (total_length : Int) (current_length : Int) (lens1_2 : (List Int)) (pivot_length : Int) (boundary : Int) (scan : Int) (PreH1 : (position < current_length)) (PreH2 : (position < total_length)) (PreH3 : ((0 : Int) <= (scan * number_width_pre))) (PreH4 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH5 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH6 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH7 : (1 <= count_pre)) (PreH8 : (count_pre <= 20)) (PreH9 : (1 <= number_width_pre)) (PreH10 : (number_width_pre <= 10)) (PreH11 : ((0 : Int) <= low_pre)) (PreH12 : (low_pre < high_pre)) (PreH13 : (high_pre < count_pre)) (PreH14 : ((low_pre - 1) <= boundary)) (PreH15 : (boundary < scan)) (PreH16 : (low_pre <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (1 <= (sum (lens)))) (PreH19 : ((sum (lens)) <= 200)) (PreH20 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH21 : (current_length = (Znth (scan) (lens1_2) ((0 : Int))))) (PreH22 : (1 <= current_length)) (PreH23 : (current_length <= number_width_pre)) (PreH24 : (1 <= pivot_length)) (PreH25 : (pivot_length <= number_width_pre)) (PreH26 : (total_length = (current_length + pivot_length))) (PreH27 : (comparison = (0 : Int))) (PreH28 : ((0 : Int) <= position)) (PreH29 : (position <= total_length)) (PreH30 : ((Zlength (rows1_2)) = count_pre)) (PreH31 : ((Zlength (lens1_2)) = count_pre)) (PreH32 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1_2)))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH34 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH35 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH36 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1_2) (lens1_2)))) (PreH38 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1_2) (lens1_2)))) (PreH39 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan)) (PreH40 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position)) (PreH41 : ((sum (lens1_2)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1_2 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1_2)
|--
  EX flat1_2 : (List Int), EX rows1 : (List (List Int)), EX lens1 : (List Int),
  “ ((0 : Int) <= (scan * number_width_pre)) ” &&
  “ (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary < scan) ” &&
  “ (low_pre <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (current_length = (Znth (scan) (lens1) ((0 : Int)))) ” &&
  “ (1 <= current_length) ” &&
  “ (current_length <= number_width_pre) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (total_length = (current_length + pivot_length)) ” &&
  “ (comparison = (0 : Int)) ” &&
  “ ((0 : Int) <= position) ” &&
  “ (position < total_length) ” &&
  “ ((Znth ((scan * number_width_pre) + position) flat1 (0 : Int)) = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position))) ” &&
  “ ((Zlength (rows1)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1))) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1 scan high_pre position) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1_2 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1_2)
  ** (intArray.full lengths_pre count_pre lens1)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1_2 : (List (List Int))) (position : Int) (comparison : Int) (total_length : Int) (current_length : Int) (lens1_2 : (List Int)) (pivot_length : Int) (boundary : Int) (scan : Int) (PreH1 : (position < current_length)) (PreH2 : (position < total_length)) (PreH3 : ((0 : Int) <= (scan * number_width_pre))) (PreH4 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH5 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH6 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH7 : (1 <= count_pre)) (PreH8 : (count_pre <= 20)) (PreH9 : (1 <= number_width_pre)) (PreH10 : (number_width_pre <= 10)) (PreH11 : ((0 : Int) <= low_pre)) (PreH12 : (low_pre < high_pre)) (PreH13 : (high_pre < count_pre)) (PreH14 : ((low_pre - 1) <= boundary)) (PreH15 : (boundary < scan)) (PreH16 : (low_pre <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (1 <= (sum (lens)))) (PreH19 : ((sum (lens)) <= 200)) (PreH20 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH21 : (current_length = (Znth (scan) (lens1_2) ((0 : Int))))) (PreH22 : (1 <= current_length)) (PreH23 : (current_length <= number_width_pre)) (PreH24 : (1 <= pivot_length)) (PreH25 : (pivot_length <= number_width_pre)) (PreH26 : (total_length = (current_length + pivot_length))) (PreH27 : (comparison = (0 : Int))) (PreH28 : ((0 : Int) <= position)) (PreH29 : (position <= total_length)) (PreH30 : ((Zlength (rows1_2)) = count_pre)) (PreH31 : ((Zlength (lens1_2)) = count_pre)) (PreH32 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1_2)))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH34 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH35 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH36 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1_2) (lens1_2)))) (PreH38 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1_2) (lens1_2)))) (PreH39 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan)) (PreH40 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position)) (PreH41 : ((sum (lens1_2)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1_2 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ ((Znth ((scan * number_width_pre) + position) flat1 (0 : Int)) = (ConcatLeftDigit (rows1) (lens1_2) (scan) (high_pre) (position))) ” &&
  “ ((Zlength (rows1)) = (Zlength (rows1_2))) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1_2))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1_2))) ” &&
  “ (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1_2 scan high_pre position) ” &&
  “ (FlatRows flat1 rows1 (Zlength (rows1_2)) number_width_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_3_2 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1_2 : (List (List Int))) (position : Int) (comparison : Int) (total_length : Int) (current_length : Int) (lens1_2 : (List Int)) (pivot_length : Int) (boundary : Int) (scan : Int) (PreH1 : (position >= current_length)) (PreH2 : (position < total_length)) (PreH3 : ((0 : Int) <= (scan * number_width_pre))) (PreH4 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH5 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH6 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH7 : (1 <= count_pre)) (PreH8 : (count_pre <= 20)) (PreH9 : (1 <= number_width_pre)) (PreH10 : (number_width_pre <= 10)) (PreH11 : ((0 : Int) <= low_pre)) (PreH12 : (low_pre < high_pre)) (PreH13 : (high_pre < count_pre)) (PreH14 : ((low_pre - 1) <= boundary)) (PreH15 : (boundary < scan)) (PreH16 : (low_pre <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (1 <= (sum (lens)))) (PreH19 : ((sum (lens)) <= 200)) (PreH20 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH21 : (current_length = (Znth (scan) (lens1_2) ((0 : Int))))) (PreH22 : (1 <= current_length)) (PreH23 : (current_length <= number_width_pre)) (PreH24 : (1 <= pivot_length)) (PreH25 : (pivot_length <= number_width_pre)) (PreH26 : (total_length = (current_length + pivot_length))) (PreH27 : (comparison = (0 : Int))) (PreH28 : ((0 : Int) <= position)) (PreH29 : (position <= total_length)) (PreH30 : ((Zlength (rows1_2)) = count_pre)) (PreH31 : ((Zlength (lens1_2)) = count_pre)) (PreH32 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1_2)))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH34 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH35 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH36 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1_2) (lens1_2)))) (PreH38 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1_2) (lens1_2)))) (PreH39 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan)) (PreH40 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position)) (PreH41 : ((sum (lens1_2)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1_2 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1_2)
|--
  EX flat1_2 : (List Int), EX rows1 : (List (List Int)), EX lens1 : (List Int),
  “ ((0 : Int) <= (scan * number_width_pre)) ” &&
  “ (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary < scan) ” &&
  “ (low_pre <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (current_length = (Znth (scan) (lens1) ((0 : Int)))) ” &&
  “ (1 <= current_length) ” &&
  “ (current_length <= number_width_pre) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (total_length = (current_length + pivot_length)) ” &&
  “ (comparison = (0 : Int)) ” &&
  “ ((0 : Int) <= position) ” &&
  “ (position < total_length) ” &&
  “ ((Znth ((high_pre * number_width_pre) + (position - current_length)) flat1 (0 : Int)) = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position))) ” &&
  “ ((Zlength (rows1)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1))) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1 scan high_pre position) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1_2 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1_2)
  ** (intArray.full lengths_pre count_pre lens1)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1_2 : (List (List Int))) (position : Int) (comparison : Int) (total_length : Int) (current_length : Int) (lens1_2 : (List Int)) (pivot_length : Int) (boundary : Int) (scan : Int) (PreH1 : (position >= current_length)) (PreH2 : (position < total_length)) (PreH3 : ((0 : Int) <= (scan * number_width_pre))) (PreH4 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH5 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH6 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH7 : (1 <= count_pre)) (PreH8 : (count_pre <= 20)) (PreH9 : (1 <= number_width_pre)) (PreH10 : (number_width_pre <= 10)) (PreH11 : ((0 : Int) <= low_pre)) (PreH12 : (low_pre < high_pre)) (PreH13 : (high_pre < count_pre)) (PreH14 : ((low_pre - 1) <= boundary)) (PreH15 : (boundary < scan)) (PreH16 : (low_pre <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (1 <= (sum (lens)))) (PreH19 : ((sum (lens)) <= 200)) (PreH20 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH21 : (current_length = (Znth (scan) (lens1_2) ((0 : Int))))) (PreH22 : (1 <= current_length)) (PreH23 : (current_length <= number_width_pre)) (PreH24 : (1 <= pivot_length)) (PreH25 : (pivot_length <= number_width_pre)) (PreH26 : (total_length = (current_length + pivot_length))) (PreH27 : (comparison = (0 : Int))) (PreH28 : ((0 : Int) <= position)) (PreH29 : (position <= total_length)) (PreH30 : ((Zlength (rows1_2)) = count_pre)) (PreH31 : ((Zlength (lens1_2)) = count_pre)) (PreH32 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1_2)))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH34 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH35 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH36 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1_2) (lens1_2)))) (PreH38 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1_2) (lens1_2)))) (PreH39 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan)) (PreH40 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position)) (PreH41 : ((sum (lens1_2)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1_2 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ ((Znth ((high_pre * number_width_pre) + (position - (Znth (scan) (lens1_2) ((0 : Int))))) flat1 (0 : Int)) = (ConcatLeftDigit (rows1) (lens1_2) (scan) (high_pre) (position))) ” &&
  “ ((Zlength (rows1)) = (Zlength (rows1_2))) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1_2))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1_2))) ” &&
  “ (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1_2 scan high_pre position) ” &&
  “ (FlatRows flat1 rows1 (Zlength (rows1_2)) number_width_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_4_1 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1 : (List Int)) (scan : Int) (boundary : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (PreH1 : (position < pivot_length)) (PreH2 : ((0 : Int) <= (scan * number_width_pre))) (PreH3 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH20 : (current_length = (Znth (scan) (lens1_2) ((0 : Int))))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length))) (PreH26 : (comparison = (0 : Int))) (PreH27 : ((0 : Int) <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) (PreH30 : ((Zlength (rows1_2)) = count_pre)) (PreH31 : ((Zlength (lens1_2)) = count_pre)) (PreH32 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1_2)))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH34 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH35 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH36 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1_2) (lens1_2)))) (PreH38 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1_2) (lens1_2)))) (PreH39 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan)) (PreH40 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position)) (PreH41 : ((sum (lens1_2)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1_2 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1_2)
|--
  EX flat1_2 : (List Int), EX rows1 : (List (List Int)), EX lens1 : (List Int),
  “ ((0 : Int) <= (scan * number_width_pre)) ” &&
  “ (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary < scan) ” &&
  “ (low_pre <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (current_length = (Znth (scan) (lens1) ((0 : Int)))) ” &&
  “ (1 <= current_length) ” &&
  “ (current_length <= number_width_pre) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (total_length = (current_length + pivot_length)) ” &&
  “ (comparison = (0 : Int)) ” &&
  “ ((0 : Int) <= position) ” &&
  “ (position < total_length) ” &&
  “ (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position))) ” &&
  “ ((Znth ((high_pre * number_width_pre) + position) flat1 (0 : Int)) = (ConcatRightDigit (rows1) (lens1) (scan) (high_pre) (position))) ” &&
  “ ((Zlength (rows1)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1))) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1 scan high_pre position) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1_2 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1_2)
  ** (intArray.full lengths_pre count_pre lens1)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1 : (List Int)) (scan : Int) (boundary : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (PreH1 : (position < pivot_length)) (PreH2 : ((0 : Int) <= (scan * number_width_pre))) (PreH3 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH20 : (current_length = (Znth (scan) (lens1_2) ((0 : Int))))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length))) (PreH26 : (comparison = (0 : Int))) (PreH27 : ((0 : Int) <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) (PreH30 : ((Zlength (rows1_2)) = count_pre)) (PreH31 : ((Zlength (lens1_2)) = count_pre)) (PreH32 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1_2)))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH34 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH35 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH36 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1_2) (lens1_2)))) (PreH38 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1_2) (lens1_2)))) (PreH39 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan)) (PreH40 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position)) (PreH41 : ((sum (lens1_2)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1_2 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ ((ConcatLeftDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)) = (ConcatLeftDigit (rows1) (lens1_2) (scan) (high_pre) (position))) ” &&
  “ ((Znth ((high_pre * number_width_pre) + position) flat1 (0 : Int)) = (ConcatRightDigit (rows1) (lens1_2) (scan) (high_pre) (position))) ” &&
  “ ((Zlength (rows1)) = (Zlength (rows1_2))) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1_2))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1_2))) ” &&
  “ (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1_2 scan high_pre position) ” &&
  “ (FlatRows flat1 rows1 (Zlength (rows1_2)) number_width_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_4_2 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1 : (List Int)) (scan : Int) (boundary : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (PreH1 : (position >= pivot_length)) (PreH2 : ((0 : Int) <= (scan * number_width_pre))) (PreH3 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH20 : (current_length = (Znth (scan) (lens1_2) ((0 : Int))))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length))) (PreH26 : (comparison = (0 : Int))) (PreH27 : ((0 : Int) <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) (PreH30 : ((Zlength (rows1_2)) = count_pre)) (PreH31 : ((Zlength (lens1_2)) = count_pre)) (PreH32 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1_2)))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH34 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH35 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH36 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1_2) (lens1_2)))) (PreH38 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1_2) (lens1_2)))) (PreH39 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan)) (PreH40 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position)) (PreH41 : ((sum (lens1_2)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1_2 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1_2)
|--
  EX flat1_2 : (List Int), EX rows1 : (List (List Int)), EX lens1 : (List Int),
  “ ((0 : Int) <= (scan * number_width_pre)) ” &&
  “ (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary < scan) ” &&
  “ (low_pre <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (current_length = (Znth (scan) (lens1) ((0 : Int)))) ” &&
  “ (1 <= current_length) ” &&
  “ (current_length <= number_width_pre) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (total_length = (current_length + pivot_length)) ” &&
  “ (comparison = (0 : Int)) ” &&
  “ ((0 : Int) <= position) ” &&
  “ (position < total_length) ” &&
  “ (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position))) ” &&
  “ ((Znth ((scan * number_width_pre) + (position - pivot_length)) flat1 (0 : Int)) = (ConcatRightDigit (rows1) (lens1) (scan) (high_pre) (position))) ” &&
  “ ((Zlength (rows1)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1))) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1 scan high_pre position) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1_2 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1_2)
  ** (intArray.full lengths_pre count_pre lens1)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1 : (List Int)) (scan : Int) (boundary : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (PreH1 : (position >= pivot_length)) (PreH2 : ((0 : Int) <= (scan * number_width_pre))) (PreH3 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH20 : (current_length = (Znth (scan) (lens1_2) ((0 : Int))))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length))) (PreH26 : (comparison = (0 : Int))) (PreH27 : ((0 : Int) <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) (PreH30 : ((Zlength (rows1_2)) = count_pre)) (PreH31 : ((Zlength (lens1_2)) = count_pre)) (PreH32 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1_2)))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH34 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH35 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH36 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1_2) (lens1_2)))) (PreH38 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1_2) (lens1_2)))) (PreH39 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan)) (PreH40 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position)) (PreH41 : ((sum (lens1_2)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1_2 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ ((ConcatLeftDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)) = (ConcatLeftDigit (rows1) (lens1_2) (scan) (high_pre) (position))) ” &&
  “ ((Znth ((scan * number_width_pre) + (position - (Znth (high_pre) (lens1_2) ((0 : Int))))) flat1 (0 : Int)) = (ConcatRightDigit (rows1) (lens1_2) (scan) (high_pre) (position))) ” &&
  “ ((Zlength (rows1)) = (Zlength (rows1_2))) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1_2))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1_2))) ” &&
  “ (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1_2 scan high_pre position) ” &&
  “ (FlatRows flat1 rows1 (Zlength (rows1_2)) number_width_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_5 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1_2 : (List Int)) (scan : Int) (boundary : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (right_digit : Int) (PreH1 : (left_digit = right_digit)) (PreH2 : ((0 : Int) <= (scan * number_width_pre))) (PreH3 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH20 : (current_length = (Znth (scan) (lens1_2) ((0 : Int))))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length))) (PreH26 : (comparison = (0 : Int))) (PreH27 : ((0 : Int) <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) (PreH30 : (right_digit = (ConcatRightDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) (PreH31 : ((Zlength (rows1_2)) = count_pre)) (PreH32 : ((Zlength (lens1_2)) = count_pre)) (PreH33 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1_2)))) (PreH34 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH35 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH36 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH37 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH38 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1_2) (lens1_2)))) (PreH39 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1_2) (lens1_2)))) (PreH40 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan)) (PreH41 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position)) (PreH42 : ((sum (lens1_2)) = (sum (lens)))) (PreH43 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1_2)
  ** (intArray.full lengths_pre count_pre lens1_2)
|--
  EX flat1 : (List Int), EX rows1 : (List (List Int)), EX lens1 : (List Int),
  “ ((0 : Int) <= (scan * number_width_pre)) ” &&
  “ (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary < scan) ” &&
  “ (low_pre <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (current_length = (Znth (scan) (lens1) ((0 : Int)))) ” &&
  “ (1 <= current_length) ” &&
  “ (current_length <= number_width_pre) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (total_length = (current_length + pivot_length)) ” &&
  “ (comparison = (0 : Int)) ” &&
  “ ((0 : Int) <= (position + 1)) ” &&
  “ ((position + 1) <= total_length) ” &&
  “ ((Zlength (rows1)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1))) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1 scan high_pre (position + 1)) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1_2 : (List Int)) (scan : Int) (boundary : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (right_digit : Int) (PreH1 : (left_digit = right_digit)) (PreH2 : ((0 : Int) <= (scan * number_width_pre))) (PreH3 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH20 : (current_length = (Znth (scan) (lens1_2) ((0 : Int))))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length))) (PreH26 : (comparison = (0 : Int))) (PreH27 : ((0 : Int) <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) (PreH30 : (right_digit = (ConcatRightDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) (PreH31 : ((Zlength (rows1_2)) = count_pre)) (PreH32 : ((Zlength (lens1_2)) = count_pre)) (PreH33 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1_2)))) (PreH34 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH35 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH36 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH37 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH38 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1_2) (lens1_2)))) (PreH39 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1_2) (lens1_2)))) (PreH40 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan)) (PreH41 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position)) (PreH42 : ((sum (lens1_2)) = (sum (lens)))) (PreH43 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ ((0 : Int) <= (position + 1)) ” &&
  “ ((position + 1) <= (current_length + pivot_length)) ” &&
  “ ((Zlength (rows1)) = (Zlength (rows1_2))) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1_2))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1_2))) ” &&
  “ (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1_2 scan high_pre (position + 1)) ” &&
  “ (FlatRows flat1_2 rows1 (Zlength (rows1_2)) number_width_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_6_1 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1_2 : (List Int)) (rows1_2 : (List (List Int))) (position : Int) (comparison : Int) (total_length : Int) (current_length : Int) (lens1_2 : (List Int)) (pivot_length : Int) (boundary : Int) (scan : Int) (PreH1 : (position >= total_length)) (PreH2 : ((0 : Int) <= (scan * number_width_pre))) (PreH3 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH20 : (current_length = (Znth (scan) (lens1_2) ((0 : Int))))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length))) (PreH26 : (comparison = (0 : Int))) (PreH27 : ((0 : Int) <= position)) (PreH28 : (position <= total_length)) (PreH29 : ((Zlength (rows1_2)) = count_pre)) (PreH30 : ((Zlength (lens1_2)) = count_pre)) (PreH31 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1_2)))) (PreH32 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH33 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH34 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH35 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH36 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1_2) (lens1_2)))) (PreH37 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1_2) (lens1_2)))) (PreH38 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan)) (PreH39 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position)) (PreH40 : ((sum (lens1_2)) = (sum (lens)))) (PreH41 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  ((( &( "position" ) )) # Int |-> (position))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1_2)
  ** (intArray.full lengths_pre count_pre lens1_2)
|--
  EX flat1 : (List Int), EX rows1 : (List (List Int)), EX lens1 : (List Int),
  “ ((0 : Int) <= (scan * number_width_pre)) ” &&
  “ (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary < scan) ” &&
  “ (low_pre <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (current_length = (Znth (scan) (lens1) ((0 : Int)))) ” &&
  “ (1 <= current_length) ” &&
  “ (current_length <= number_width_pre) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (total_length = (current_length + pivot_length)) ” &&
  “ ((Zlength (rows1)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1))) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan) ” &&
  “ (ConcatCompareOutcome rows1 lens1 scan high_pre comparison) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "position" ) )) # Int |->_)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1_2 : (List Int)) (rows1_2 : (List (List Int))) (position : Int) (comparison : Int) (total_length : Int) (current_length : Int) (lens1_2 : (List Int)) (pivot_length : Int) (boundary : Int) (scan : Int) (PreH1 : (position >= total_length)) (PreH2 : ((0 : Int) <= (scan * number_width_pre))) (PreH3 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH20 : (current_length = (Znth (scan) (lens1_2) ((0 : Int))))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length))) (PreH26 : (comparison = (0 : Int))) (PreH27 : ((0 : Int) <= position)) (PreH28 : (position <= total_length)) (PreH29 : ((Zlength (rows1_2)) = count_pre)) (PreH30 : ((Zlength (lens1_2)) = count_pre)) (PreH31 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1_2)))) (PreH32 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH33 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH34 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH35 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH36 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1_2) (lens1_2)))) (PreH37 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1_2) (lens1_2)))) (PreH38 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan)) (PreH39 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position)) (PreH40 : ((sum (lens1_2)) = (sum (lens)))) (PreH41 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ ((Zlength (rows1)) = (Zlength (rows1_2))) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1_2))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1_2))) ” &&
  “ (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan) ” &&
  “ (ConcatCompareOutcome rows1 lens1_2 scan high_pre (0 : Int)) ” &&
  “ (FlatRows flat1_2 rows1 (Zlength (rows1_2)) number_width_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_6_2 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1_2 : (List Int)) (scan : Int) (boundary : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (right_digit : Int) (PreH1 : (left_digit ≠ right_digit)) (PreH2 : ((0 : Int) <= (scan * number_width_pre))) (PreH3 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH20 : (current_length = (Znth (scan) (lens1_2) ((0 : Int))))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length))) (PreH26 : (comparison = (0 : Int))) (PreH27 : ((0 : Int) <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) (PreH30 : (right_digit = (ConcatRightDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) (PreH31 : ((Zlength (rows1_2)) = count_pre)) (PreH32 : ((Zlength (lens1_2)) = count_pre)) (PreH33 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1_2)))) (PreH34 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH35 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH36 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH37 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH38 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1_2) (lens1_2)))) (PreH39 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1_2) (lens1_2)))) (PreH40 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan)) (PreH41 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position)) (PreH42 : ((sum (lens1_2)) = (sum (lens)))) (PreH43 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  ((( &( "position" ) )) # Int |-> (position))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1_2)
  ** (intArray.full lengths_pre count_pre lens1_2)
|--
  EX flat1 : (List Int), EX rows1 : (List (List Int)), EX lens1 : (List Int),
  “ ((0 : Int) <= (scan * number_width_pre)) ” &&
  “ (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary < scan) ” &&
  “ (low_pre <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (current_length = (Znth (scan) (lens1) ((0 : Int)))) ” &&
  “ (1 <= current_length) ” &&
  “ (current_length <= number_width_pre) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (total_length = (current_length + pivot_length)) ” &&
  “ ((Zlength (rows1)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1))) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan) ” &&
  “ (ConcatCompareOutcome rows1 lens1 scan high_pre (left_digit - right_digit)) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "position" ) )) # Int |->_)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1_2 : (List Int)) (scan : Int) (boundary : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (right_digit : Int) (PreH1 : (left_digit ≠ right_digit)) (PreH2 : ((0 : Int) <= (scan * number_width_pre))) (PreH3 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH20 : (current_length = (Znth (scan) (lens1_2) ((0 : Int))))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length))) (PreH26 : (comparison = (0 : Int))) (PreH27 : ((0 : Int) <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) (PreH30 : (right_digit = (ConcatRightDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) (PreH31 : ((Zlength (rows1_2)) = count_pre)) (PreH32 : ((Zlength (lens1_2)) = count_pre)) (PreH33 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1_2)))) (PreH34 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH35 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH36 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH37 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH38 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1_2) (lens1_2)))) (PreH39 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1_2) (lens1_2)))) (PreH40 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan)) (PreH41 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position)) (PreH42 : ((sum (lens1_2)) = (sum (lens)))) (PreH43 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ ((Zlength (rows1)) = (Zlength (rows1_2))) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1_2))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1_2))) ” &&
  “ (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan) ” &&
  “ (ConcatCompareOutcome rows1 lens1_2 scan high_pre ((ConcatLeftDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)) - (ConcatRightDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) ” &&
  “ (FlatRows flat1_2 rows1 (Zlength (rows1_2)) number_width_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_7 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1_2 : (List Int)) (flat1 : (List Int)) (scan : Int) (boundary : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (PreH1 : (comparison > (0 : Int))) (PreH2 : ((0 : Int) <= (scan * number_width_pre))) (PreH3 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH20 : (current_length = (Znth (scan) (lens1_2) ((0 : Int))))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length))) (PreH26 : ((Zlength (rows1)) = count_pre)) (PreH27 : ((Zlength (lens1_2)) = count_pre)) (PreH28 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH29 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH30 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH31 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH32 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH33 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1_2)))) (PreH34 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1_2)))) (PreH35 : (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan)) (PreH36 : (ConcatCompareOutcome rows1 lens1_2 scan high_pre comparison)) (PreH37 : ((sum (lens1_2)) = (sum (lens)))) (PreH38 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1_2)
|--
  EX flat_now : (List Int), EX rows_now : (List (List Int)), EX rows_before : (List (List Int)), EX lens1 : (List Int),
  “ ((0 : Int) <= ((boundary + 1) * number_width_pre)) ” &&
  “ ((((boundary + 1) * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (scan * number_width_pre)) ” &&
  “ (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= (boundary + 1)) ” &&
  “ ((boundary + 1) <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ ((Zlength (rows_before)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre ((boundary + 1) - 1) scan) ” &&
  “ (ConcatCompareOutcome rows_before lens1 scan high_pre comparison) ” &&
  “ (comparison > (0 : Int)) ” &&
  “ (SwapRowsPrefix rows_before rows_now (boundary + 1) scan (0 : Int) number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |->_)
  ** ((( &( "total_length" ) )) # Int |->_)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1_2 : (List Int)) (flat1 : (List Int)) (scan : Int) (boundary : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (PreH1 : (comparison > (0 : Int))) (PreH2 : ((0 : Int) <= (scan * number_width_pre))) (PreH3 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH20 : (current_length = (Znth (scan) (lens1_2) ((0 : Int))))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length))) (PreH26 : ((Zlength (rows1)) = count_pre)) (PreH27 : ((Zlength (lens1_2)) = count_pre)) (PreH28 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH29 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH30 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH31 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH32 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH33 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1_2)))) (PreH34 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1_2)))) (PreH35 : (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan)) (PreH36 : (ConcatCompareOutcome rows1 lens1_2 scan high_pre comparison)) (PreH37 : ((sum (lens1_2)) = (sum (lens)))) (PreH38 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows_now : (List (List Int)), EX rows_before : (List (List Int)),
  “ ((0 : Int) <= ((boundary + 1) * number_width_pre)) ” &&
  “ ((((boundary + 1) * number_width_pre) + number_width_pre) <= ((Zlength (rows1)) * number_width_pre)) ” &&
  “ (low_pre <= (boundary + 1)) ” &&
  “ ((boundary + 1) <= scan) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= number_width_pre) ” &&
  “ ((Zlength (rows_before)) = (Zlength (rows1))) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1_2))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1_2))) ” &&
  “ (PartitionScanState rows rows_before lens lens1_2 low_pre high_pre ((boundary + 1) - 1) scan) ” &&
  “ (ConcatCompareOutcome rows_before lens1_2 scan high_pre comparison) ” &&
  “ (SwapRowsPrefix rows_before rows_now (boundary + 1) scan (0 : Int) number_width_pre) ” &&
  “ (FlatRows flat1 rows_now (Zlength (rows1)) number_width_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_8 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now_2 : (List Int)) (rows_now_2 : (List (List Int))) (comparison : Int) (rows_before_2 : (List (List Int))) (lens1_2 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : (column < number_width_pre)) (PreH2 : ((0 : Int) <= (boundary * number_width_pre))) (PreH3 : (((boundary * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (scan * number_width_pre))) (PreH5 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH7 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : ((0 : Int) <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : ((0 : Int) <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before_2)) = count_pre)) (PreH26 : ((Zlength (lens1_2)) = count_pre)) (PreH27 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before_2)))) (PreH28 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH29 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before_2)))) (PreH31 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before_2)))) (PreH32 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before_2) (lens1_2)))) (PreH33 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before_2) (lens1_2)))) (PreH34 : (PartitionScanState rows rows_before_2 lens lens1_2 low_pre high_pre (boundary - 1) scan)) (PreH35 : (ConcatCompareOutcome rows_before_2 lens1_2 scan high_pre comparison)) (PreH36 : (comparison > (0 : Int))) (PreH37 : (SwapRowsPrefix rows_before_2 rows_now_2 boundary scan column number_width_pre)) (PreH38 : ((sum (lens1_2)) = (sum (lens)))) (PreH39 : (FlatRows flat_now_2 rows_now_2 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) (replace_Znth (((scan * number_width_pre) + column)) ((Znth ((boundary * number_width_pre) + column) flat_now_2 (0 : Int))) ((replace_Znth (((boundary * number_width_pre) + column)) ((Znth ((scan * number_width_pre) + column) flat_now_2 (0 : Int))) (flat_now_2)))))
  ** (intArray.full lengths_pre count_pre lens1_2)
|--
  EX flat_now : (List Int), EX rows_now : (List (List Int)), EX rows_before : (List (List Int)), EX lens1 : (List Int),
  “ ((0 : Int) <= (boundary * number_width_pre)) ” &&
  “ (((boundary * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (scan * number_width_pre)) ” &&
  “ (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= boundary) ” &&
  “ (boundary <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ ((0 : Int) <= (column + 1)) ” &&
  “ ((column + 1) <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ ((Zlength (rows_before)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan) ” &&
  “ (ConcatCompareOutcome rows_before lens1 scan high_pre comparison) ” &&
  “ (comparison > (0 : Int)) ” &&
  “ (SwapRowsPrefix rows_before rows_now boundary scan (column + 1) number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now_2 : (List Int)) (rows_now_2 : (List (List Int))) (comparison : Int) (rows_before_2 : (List (List Int))) (lens1_2 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : (column < number_width_pre)) (PreH2 : ((0 : Int) <= (boundary * number_width_pre))) (PreH3 : (((boundary * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (scan * number_width_pre))) (PreH5 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH7 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : ((0 : Int) <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : ((0 : Int) <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before_2)) = count_pre)) (PreH26 : ((Zlength (lens1_2)) = count_pre)) (PreH27 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before_2)))) (PreH28 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH29 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before_2)))) (PreH31 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before_2)))) (PreH32 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before_2) (lens1_2)))) (PreH33 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before_2) (lens1_2)))) (PreH34 : (PartitionScanState rows rows_before_2 lens lens1_2 low_pre high_pre (boundary - 1) scan)) (PreH35 : (ConcatCompareOutcome rows_before_2 lens1_2 scan high_pre comparison)) (PreH36 : (comparison > (0 : Int))) (PreH37 : (SwapRowsPrefix rows_before_2 rows_now_2 boundary scan column number_width_pre)) (PreH38 : ((sum (lens1_2)) = (sum (lens)))) (PreH39 : (FlatRows flat_now_2 rows_now_2 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows_now : (List (List Int)), EX rows_before : (List (List Int)),
  “ ((0 : Int) <= (column + 1)) ” &&
  “ ((column + 1) <= number_width_pre) ” &&
  “ ((Zlength (rows_before)) = (Zlength (rows_before_2))) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1_2))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1_2))) ” &&
  “ (PartitionScanState rows rows_before lens lens1_2 low_pre high_pre (boundary - 1) scan) ” &&
  “ (ConcatCompareOutcome rows_before lens1_2 scan high_pre comparison) ” &&
  “ (SwapRowsPrefix rows_before rows_now boundary scan (column + 1) number_width_pre) ” &&
  “ (FlatRows (replace_Znth (((scan * number_width_pre) + column)) ((Znth ((boundary * number_width_pre) + column) flat_now_2 (0 : Int))) ((replace_Znth (((boundary * number_width_pre) + column)) ((Znth ((scan * number_width_pre) + column) flat_now_2 (0 : Int))) (flat_now_2)))) rows_now (Zlength (rows_before_2)) number_width_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_9_1 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1_2 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : (column >= number_width_pre)) (PreH2 : ((0 : Int) <= (boundary * number_width_pre))) (PreH3 : (((boundary * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (scan * number_width_pre))) (PreH5 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH7 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : ((0 : Int) <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : ((0 : Int) <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1_2)) = count_pre)) (PreH27 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before)))) (PreH28 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH29 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH31 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH32 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1_2)))) (PreH33 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1_2)))) (PreH34 : (PartitionScanState rows rows_before lens lens1_2 low_pre high_pre (boundary - 1) scan)) (PreH35 : (ConcatCompareOutcome rows_before lens1_2 scan high_pre comparison)) (PreH36 : (comparison > (0 : Int))) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH38 : ((sum (lens1_2)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full lengths_pre count_pre (replace_Znth (scan) ((Znth boundary lens1_2 (0 : Int))) ((replace_Znth (boundary) ((Znth scan lens1_2 (0 : Int))) (lens1_2)))))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
|--
  EX flat1 : (List Int), EX rows1 : (List (List Int)), EX lens1 : (List Int),
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ ((Zlength (rows1)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1))) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary (scan + 1)) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "comparison" ) )) # Int |->_)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1_2 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : (column >= number_width_pre)) (PreH2 : ((0 : Int) <= (boundary * number_width_pre))) (PreH3 : (((boundary * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (scan * number_width_pre))) (PreH5 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH7 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : ((0 : Int) <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : ((0 : Int) <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1_2)) = count_pre)) (PreH27 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before)))) (PreH28 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH29 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH31 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH32 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1_2)))) (PreH33 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1_2)))) (PreH34 : (PartitionScanState rows rows_before lens lens1_2 low_pre high_pre (boundary - 1) scan)) (PreH35 : (ConcatCompareOutcome rows_before lens1_2 scan high_pre comparison)) (PreH36 : (comparison > (0 : Int))) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH38 : ((sum (lens1_2)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ ((low_pre - 1) <= boundary) ” &&
  “ ((Znth (high_pre) (lens1_2) ((0 : Int))) = (Znth (high_pre) ((replace_Znth (scan) ((Znth boundary lens1_2 (0 : Int))) ((replace_Znth (boundary) ((Znth scan lens1_2 (0 : Int))) (lens1_2))))) ((0 : Int)))) ” &&
  “ ((Zlength (rows1)) = (Zlength (rows_before))) ” &&
  “ ((Zlength ((replace_Znth (scan) ((Znth boundary lens1_2 (0 : Int))) ((replace_Znth (boundary) ((Znth scan lens1_2 (0 : Int))) (lens1_2)))))) = (Zlength (rows_before))) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (replace_Znth (scan) ((Znth boundary lens1_2 (0 : Int))) ((replace_Znth (boundary) ((Znth scan lens1_2 (0 : Int))) (lens1_2))))) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) (replace_Znth (scan) ((Znth boundary lens1_2 (0 : Int))) ((replace_Znth (boundary) ((Znth scan lens1_2 (0 : Int))) (lens1_2))))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) ((replace_Znth (scan) ((Znth boundary lens1_2 (0 : Int))) ((replace_Znth (boundary) ((Znth scan lens1_2 (0 : Int))) (lens1_2))))))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) ((replace_Znth (scan) ((Znth boundary lens1_2 (0 : Int))) ((replace_Znth (boundary) ((Znth scan lens1_2 (0 : Int))) (lens1_2))))))) ” &&
  “ (PartitionScanState rows rows1 lens (replace_Znth (scan) ((Znth boundary lens1_2 (0 : Int))) ((replace_Znth (boundary) ((Znth scan lens1_2 (0 : Int))) (lens1_2)))) low_pre high_pre boundary (scan + 1)) ” &&
  “ ((sum ((replace_Znth (scan) ((Znth boundary lens1_2 (0 : Int))) ((replace_Znth (boundary) ((Znth scan lens1_2 (0 : Int))) (lens1_2)))))) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows1 (Zlength (rows_before)) number_width_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_9_2 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1_2 : (List Int)) (scan : Int) (boundary : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (PreH1 : (comparison <= (0 : Int))) (PreH2 : ((0 : Int) <= (scan * number_width_pre))) (PreH3 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH20 : (current_length = (Znth (scan) (lens1_2) ((0 : Int))))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length))) (PreH26 : ((Zlength (rows1_2)) = count_pre)) (PreH27 : ((Zlength (lens1_2)) = count_pre)) (PreH28 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1_2)))) (PreH29 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH30 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH31 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH32 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH33 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1_2) (lens1_2)))) (PreH34 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1_2) (lens1_2)))) (PreH35 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan)) (PreH36 : (ConcatCompareOutcome rows1_2 lens1_2 scan high_pre comparison)) (PreH37 : ((sum (lens1_2)) = (sum (lens)))) (PreH38 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  ((( &( "current_length" ) )) # Int |-> (current_length))
  ** ((( &( "total_length" ) )) # Int |-> (total_length))
  ** ((( &( "comparison" ) )) # Int |-> (comparison))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1_2)
  ** (intArray.full lengths_pre count_pre lens1_2)
|--
  EX flat1 : (List Int), EX rows1 : (List (List Int)), EX lens1 : (List Int),
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ ((Zlength (rows1)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1))) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary (scan + 1)) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "current_length" ) )) # Int |->_)
  ** ((( &( "total_length" ) )) # Int |->_)
  ** ((( &( "comparison" ) )) # Int |->_)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1_2 : (List Int)) (scan : Int) (boundary : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (PreH1 : (comparison <= (0 : Int))) (PreH2 : ((0 : Int) <= (scan * number_width_pre))) (PreH3 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH20 : (current_length = (Znth (scan) (lens1_2) ((0 : Int))))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length))) (PreH26 : ((Zlength (rows1_2)) = count_pre)) (PreH27 : ((Zlength (lens1_2)) = count_pre)) (PreH28 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1_2)))) (PreH29 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH30 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH31 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH32 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH33 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1_2) (lens1_2)))) (PreH34 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1_2) (lens1_2)))) (PreH35 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan)) (PreH36 : (ConcatCompareOutcome rows1_2 lens1_2 scan high_pre comparison)) (PreH37 : ((sum (lens1_2)) = (sum (lens)))) (PreH38 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ (boundary <= scan) ” &&
  “ ((Zlength (rows1)) = (Zlength (rows1_2))) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1_2))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1_2))) ” &&
  “ (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary (scan + 1)) ” &&
  “ (FlatRows flat1_2 rows1 (Zlength (rows1_2)) number_width_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_10 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1_2 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (PreH1 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH2 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : ((0 : Int) <= low_pre)) (PreH8 : (low_pre < high_pre)) (PreH9 : (high_pre < count_pre)) (PreH10 : ((low_pre - 1) <= boundary)) (PreH11 : (boundary <= scan)) (PreH12 : (scan < high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH16 : (1 <= pivot_length)) (PreH17 : (pivot_length <= number_width_pre)) (PreH18 : ((Zlength (rows1_2)) = count_pre)) (PreH19 : ((Zlength (lens1_2)) = count_pre)) (PreH20 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1_2)))) (PreH21 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH22 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH23 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH24 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1_2) (lens1_2)))) (PreH26 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1_2) (lens1_2)))) (PreH27 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary (scan + 1))) (PreH28 : ((sum (lens1_2)) = (sum (lens)))) (PreH29 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1_2)
  ** (intArray.full lengths_pre count_pre lens1_2)
|--
  EX flat1 : (List Int), EX rows1 : (List (List Int)), EX lens1 : (List Int),
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary < (scan + 1)) ” &&
  “ (low_pre <= (scan + 1)) ” &&
  “ ((scan + 1) <= high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ ((Zlength (rows1)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1))) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary (scan + 1)) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1_2 : (List Int)) (boundary : Int) (scan : Int) (pivot_length : Int) (PreH1 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH2 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : ((0 : Int) <= low_pre)) (PreH8 : (low_pre < high_pre)) (PreH9 : (high_pre < count_pre)) (PreH10 : ((low_pre - 1) <= boundary)) (PreH11 : (boundary <= scan)) (PreH12 : (scan < high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH16 : (1 <= pivot_length)) (PreH17 : (pivot_length <= number_width_pre)) (PreH18 : ((Zlength (rows1_2)) = count_pre)) (PreH19 : ((Zlength (lens1_2)) = count_pre)) (PreH20 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1_2)))) (PreH21 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH22 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH23 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH24 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1_2) (lens1_2)))) (PreH26 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1_2) (lens1_2)))) (PreH27 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary (scan + 1))) (PreH28 : ((sum (lens1_2)) = (sum (lens)))) (PreH29 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ (boundary < (scan + 1)) ” &&
  “ (low_pre <= (scan + 1)) ” &&
  “ ((scan + 1) <= high_pre) ” &&
  “ ((Zlength (rows1)) = (Zlength (rows1_2))) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1_2))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1_2))) ” &&
  “ (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary (scan + 1)) ” &&
  “ (FlatRows flat1_2 rows1 (Zlength (rows1_2)) number_width_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_11 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (lens1_2 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : (scan >= high_pre)) (PreH2 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH3 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : ((0 : Int) <= low_pre)) (PreH9 : (low_pre < high_pre)) (PreH10 : (high_pre < count_pre)) (PreH11 : ((low_pre - 1) <= boundary)) (PreH12 : (boundary < scan)) (PreH13 : (low_pre <= scan)) (PreH14 : (scan <= high_pre)) (PreH15 : (1 <= (sum (lens)))) (PreH16 : ((sum (lens)) <= 200)) (PreH17 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH18 : (1 <= pivot_length)) (PreH19 : (pivot_length <= number_width_pre)) (PreH20 : ((Zlength (rows1)) = count_pre)) (PreH21 : ((Zlength (lens1_2)) = count_pre)) (PreH22 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH23 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH24 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH25 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH26 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH27 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1_2)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1_2)))) (PreH29 : (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan)) (PreH30 : ((sum (lens1_2)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "boundary" ) )) # Int |-> (boundary))
  ** ((( &( "scan" ) )) # Int |-> (scan))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1_2)
|--
  EX flat_now : (List Int), EX rows_now : (List (List Int)), EX rows_before : (List (List Int)), EX lens1 : (List Int),
  “ ((0 : Int) <= ((boundary + 1) * number_width_pre)) ” &&
  “ ((((boundary + 1) * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= (boundary + 1)) ” &&
  “ ((boundary + 1) <= high_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ ((Zlength (rows_before)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre ((boundary + 1) - 1) high_pre) ” &&
  “ (SwapRowsPrefix rows_before rows_now (boundary + 1) high_pre (0 : Int) number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (lens1_2 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : (scan >= high_pre)) (PreH2 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH3 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : ((0 : Int) <= low_pre)) (PreH9 : (low_pre < high_pre)) (PreH10 : (high_pre < count_pre)) (PreH11 : ((low_pre - 1) <= boundary)) (PreH12 : (boundary < scan)) (PreH13 : (low_pre <= scan)) (PreH14 : (scan <= high_pre)) (PreH15 : (1 <= (sum (lens)))) (PreH16 : ((sum (lens)) <= 200)) (PreH17 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH18 : (1 <= pivot_length)) (PreH19 : (pivot_length <= number_width_pre)) (PreH20 : ((Zlength (rows1)) = count_pre)) (PreH21 : ((Zlength (lens1_2)) = count_pre)) (PreH22 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH23 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH24 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH25 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH26 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH27 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1_2)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1_2)))) (PreH29 : (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan)) (PreH30 : ((sum (lens1_2)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows_now : (List (List Int)), EX rows_before : (List (List Int)),
  “ ((0 : Int) <= ((boundary + 1) * number_width_pre)) ” &&
  “ ((((boundary + 1) * number_width_pre) + number_width_pre) <= ((Zlength (rows1)) * number_width_pre)) ” &&
  “ (low_pre <= (boundary + 1)) ” &&
  “ ((boundary + 1) <= high_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= number_width_pre) ” &&
  “ ((Zlength (rows_before)) = (Zlength (rows1))) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1_2))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1_2))) ” &&
  “ (PartitionScanState rows rows_before lens lens1_2 low_pre high_pre ((boundary + 1) - 1) high_pre) ” &&
  “ (SwapRowsPrefix rows_before rows_now (boundary + 1) high_pre (0 : Int) number_width_pre) ” &&
  “ (FlatRows flat1 rows_now (Zlength (rows1)) number_width_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_12 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now_2 : (List Int)) (rows_now_2 : (List (List Int))) (rows_before_2 : (List (List Int))) (lens1_2 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : (column < number_width_pre)) (PreH2 : ((0 : Int) <= (pivot * number_width_pre))) (PreH3 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : ((0 : Int) <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before_2)) = count_pre)) (PreH23 : ((Zlength (lens1_2)) = count_pre)) (PreH24 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before_2)))) (PreH25 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH26 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH27 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before_2)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before_2)))) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before_2) (lens1_2)))) (PreH30 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before_2) (lens1_2)))) (PreH31 : (PartitionScanState rows rows_before_2 lens lens1_2 low_pre high_pre (pivot - 1) high_pre)) (PreH32 : (SwapRowsPrefix rows_before_2 rows_now_2 pivot high_pre column number_width_pre)) (PreH33 : ((sum (lens1_2)) = (sum (lens)))) (PreH34 : (FlatRows flat_now_2 rows_now_2 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) (replace_Znth (((high_pre * number_width_pre) + column)) ((Znth ((pivot * number_width_pre) + column) flat_now_2 (0 : Int))) ((replace_Znth (((pivot * number_width_pre) + column)) ((Znth ((high_pre * number_width_pre) + column) flat_now_2 (0 : Int))) (flat_now_2)))))
  ** (intArray.full lengths_pre count_pre lens1_2)
|--
  EX flat_now : (List Int), EX rows_now : (List (List Int)), EX rows_before : (List (List Int)), EX lens1 : (List Int),
  “ ((0 : Int) <= (pivot * number_width_pre)) ” &&
  “ (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= pivot) ” &&
  “ (pivot <= high_pre) ” &&
  “ ((0 : Int) <= (column + 1)) ” &&
  “ ((column + 1) <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ ((Zlength (rows_before)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre) ” &&
  “ (SwapRowsPrefix rows_before rows_now pivot high_pre (column + 1) number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now_2 : (List Int)) (rows_now_2 : (List (List Int))) (rows_before_2 : (List (List Int))) (lens1_2 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : (column < number_width_pre)) (PreH2 : ((0 : Int) <= (pivot * number_width_pre))) (PreH3 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : ((0 : Int) <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before_2)) = count_pre)) (PreH23 : ((Zlength (lens1_2)) = count_pre)) (PreH24 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before_2)))) (PreH25 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH26 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH27 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before_2)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before_2)))) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before_2) (lens1_2)))) (PreH30 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before_2) (lens1_2)))) (PreH31 : (PartitionScanState rows rows_before_2 lens lens1_2 low_pre high_pre (pivot - 1) high_pre)) (PreH32 : (SwapRowsPrefix rows_before_2 rows_now_2 pivot high_pre column number_width_pre)) (PreH33 : ((sum (lens1_2)) = (sum (lens)))) (PreH34 : (FlatRows flat_now_2 rows_now_2 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows_now : (List (List Int)), EX rows_before : (List (List Int)),
  “ ((0 : Int) <= (column + 1)) ” &&
  “ ((column + 1) <= number_width_pre) ” &&
  “ ((Zlength (rows_before)) = (Zlength (rows_before_2))) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1_2))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1_2))) ” &&
  “ (PartitionScanState rows rows_before lens lens1_2 low_pre high_pre (pivot - 1) high_pre) ” &&
  “ (SwapRowsPrefix rows_before rows_now pivot high_pre (column + 1) number_width_pre) ” &&
  “ (FlatRows (replace_Znth (((high_pre * number_width_pre) + column)) ((Znth ((pivot * number_width_pre) + column) flat_now_2 (0 : Int))) ((replace_Znth (((pivot * number_width_pre) + column)) ((Znth ((high_pre * number_width_pre) + column) flat_now_2 (0 : Int))) (flat_now_2)))) rows_now (Zlength (rows_before_2)) number_width_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_entail_wit_13 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1_2 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : (column >= number_width_pre)) (PreH2 : ((0 : Int) <= (pivot * number_width_pre))) (PreH3 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : ((0 : Int) <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before)) = count_pre)) (PreH23 : ((Zlength (lens1_2)) = count_pre)) (PreH24 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before)))) (PreH25 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH26 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH27 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1_2)))) (PreH30 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1_2)))) (PreH31 : (PartitionScanState rows rows_before lens lens1_2 low_pre high_pre (pivot - 1) high_pre)) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH33 : ((sum (lens1_2)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full lengths_pre count_pre (replace_Znth (pivot) (pivot_length) ((replace_Znth (high_pre) ((Znth pivot lens1_2 (0 : Int))) (lens1_2)))))
  ** ((( &( "pivot_length" ) )) # Int |-> (pivot_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
|--
  EX flat1 : (List Int), EX lens1 : (List Int), EX rows1 : (List (List Int)),
  “ ((0 : Int) <= (pivot * number_width_pre)) ” &&
  “ (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= pivot) ” &&
  “ (pivot <= high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ ((Zlength (rows1)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1))) ” &&
  “ (PairedPermutation rows rows1 lens lens1) ” &&
  “ (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre) ” &&
  “ (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "pivot_length" ) )) # Int |->_)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1_2 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : (column >= number_width_pre)) (PreH2 : ((0 : Int) <= (pivot * number_width_pre))) (PreH3 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : ((0 : Int) <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int))))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before)) = count_pre)) (PreH23 : ((Zlength (lens1_2)) = count_pre)) (PreH24 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before)))) (PreH25 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH26 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH27 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1_2)))) (PreH30 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1_2)))) (PreH31 : (PartitionScanState rows rows_before lens lens1_2 low_pre high_pre (pivot - 1) high_pre)) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH33 : ((sum (lens1_2)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ ((Zlength (rows1)) = (Zlength (rows_before))) ” &&
  “ ((Zlength ((replace_Znth (pivot) ((Znth (high_pre) (lens1_2) ((0 : Int)))) ((replace_Znth (high_pre) ((Znth pivot lens1_2 (0 : Int))) (lens1_2)))))) = (Zlength (rows_before))) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (replace_Znth (pivot) ((Znth (high_pre) (lens1_2) ((0 : Int)))) ((replace_Znth (high_pre) ((Znth pivot lens1_2 (0 : Int))) (lens1_2))))) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) (replace_Znth (pivot) ((Znth (high_pre) (lens1_2) ((0 : Int)))) ((replace_Znth (high_pre) ((Znth pivot lens1_2 (0 : Int))) (lens1_2))))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) ((replace_Znth (pivot) ((Znth (high_pre) (lens1_2) ((0 : Int)))) ((replace_Znth (high_pre) ((Znth pivot lens1_2 (0 : Int))) (lens1_2))))))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) ((replace_Znth (pivot) ((Znth (high_pre) (lens1_2) ((0 : Int)))) ((replace_Znth (high_pre) ((Znth pivot lens1_2 (0 : Int))) (lens1_2))))))) ” &&
  “ (PairedPermutation rows rows1 lens (replace_Znth (pivot) ((Znth (high_pre) (lens1_2) ((0 : Int)))) ((replace_Znth (high_pre) ((Znth pivot lens1_2 (0 : Int))) (lens1_2))))) ” &&
  “ (SameOutsidePairedRange rows rows1 lens (replace_Znth (pivot) ((Znth (high_pre) (lens1_2) ((0 : Int)))) ((replace_Znth (high_pre) ((Znth pivot lens1_2 (0 : Int))) (lens1_2)))) low_pre high_pre) ” &&
  “ (GreedyPartitionedAt rows1 (replace_Znth (pivot) ((Znth (high_pre) (lens1_2) ((0 : Int)))) ((replace_Znth (high_pre) ((Znth pivot lens1_2 (0 : Int))) (lens1_2)))) low_pre high_pre pivot) ” &&
  “ ((sum ((replace_Znth (pivot) ((Znth (high_pre) (lens1_2) ((0 : Int)))) ((replace_Znth (high_pre) ((Znth pivot lens1_2 (0 : Int))) (lens1_2)))))) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows1 (Zlength (rows_before)) number_width_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_return_wit_1 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1_2 : (List Int)) (rows2 : (List (List Int))) (lens2 : (List Int)) (flat2 : (List Int)) (lens1_3 : (List Int)) (flat1_3 : (List Int)) (rows1_3 : (List (List Int))) (PreH1 : (FlatRows flat1_3 rows1_3 count_pre number_width_pre)) (PreH2 : (PairedPermutation rows2 rows1_3 lens2 lens1_3)) (PreH3 : (SameOutsidePairedRange rows2 rows1_3 lens2 lens1_3 (pivot + 1) high_pre)) (PreH4 : (GreedySortedRange rows1_3 lens1_3 (pivot + 1) high_pre)) (PreH5 : (pivot < high_pre)) (PreH6 : (FlatRows flat2 rows2 count_pre number_width_pre)) (PreH7 : (PairedPermutation rows1_2 rows2 lens1_2 lens2)) (PreH8 : (SameOutsidePairedRange rows1_2 rows2 lens1_2 lens2 low_pre (pivot - 1))) (PreH9 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1))) (PreH10 : (pivot > low_pre)) (PreH11 : ((0 : Int) <= (pivot * number_width_pre))) (PreH12 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH13 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH14 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH15 : (1 <= count_pre)) (PreH16 : (count_pre <= 20)) (PreH17 : (1 <= number_width_pre)) (PreH18 : (number_width_pre <= 10)) (PreH19 : ((0 : Int) <= low_pre)) (PreH20 : (low_pre < high_pre)) (PreH21 : (high_pre < count_pre)) (PreH22 : (low_pre <= pivot)) (PreH23 : (pivot <= high_pre)) (PreH24 : (1 <= (sum (lens)))) (PreH25 : ((sum (lens)) <= 200)) (PreH26 : ((Zlength (rows1_2)) = count_pre)) (PreH27 : ((Zlength (lens1_2)) = count_pre)) (PreH28 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1_2)))) (PreH29 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH30 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH31 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH32 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH33 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1_2) (lens1_2)))) (PreH34 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1_2) (lens1_2)))) (PreH35 : (PairedPermutation rows rows1_2 lens lens1_2)) (PreH36 : (SameOutsidePairedRange rows rows1_2 lens lens1_2 low_pre high_pre)) (PreH37 : (GreedyPartitionedAt rows1_2 lens1_2 low_pre high_pre pivot)) (PreH38 : ((sum (lens1_2)) = (sum (lens)))) (PreH39 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1_3)
  ** (intArray.full lengths_pre count_pre lens1_3)
|--
  EX lens1 : (List Int), EX flat1 : (List Int), EX rows1 : (List (List Int)),
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens lens1) ” &&
  “ (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre) ” &&
  “ (GreedySortedRange rows1 lens1 low_pre high_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1_2 : (List Int)) (rows2 : (List (List Int))) (lens2 : (List Int)) (flat2 : (List Int)) (lens1_3 : (List Int)) (flat1_3 : (List Int)) (rows1_3 : (List (List Int))) (PreH1 : (FlatRows flat1_3 rows1_3 count_pre number_width_pre)) (PreH2 : (PairedPermutation rows2 rows1_3 lens2 lens1_3)) (PreH3 : (SameOutsidePairedRange rows2 rows1_3 lens2 lens1_3 (pivot + 1) high_pre)) (PreH4 : (GreedySortedRange rows1_3 lens1_3 (pivot + 1) high_pre)) (PreH5 : (pivot < high_pre)) (PreH6 : (FlatRows flat2 rows2 count_pre number_width_pre)) (PreH7 : (PairedPermutation rows1_2 rows2 lens1_2 lens2)) (PreH8 : (SameOutsidePairedRange rows1_2 rows2 lens1_2 lens2 low_pre (pivot - 1))) (PreH9 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1))) (PreH10 : (pivot > low_pre)) (PreH11 : ((0 : Int) <= (pivot * number_width_pre))) (PreH12 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH13 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH14 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH15 : (1 <= count_pre)) (PreH16 : (count_pre <= 20)) (PreH17 : (1 <= number_width_pre)) (PreH18 : (number_width_pre <= 10)) (PreH19 : ((0 : Int) <= low_pre)) (PreH20 : (low_pre < high_pre)) (PreH21 : (high_pre < count_pre)) (PreH22 : (low_pre <= pivot)) (PreH23 : (pivot <= high_pre)) (PreH24 : (1 <= (sum (lens)))) (PreH25 : ((sum (lens)) <= 200)) (PreH26 : ((Zlength (rows1_2)) = count_pre)) (PreH27 : ((Zlength (lens1_2)) = count_pre)) (PreH28 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1_2)))) (PreH29 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH30 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH31 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH32 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH33 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1_2) (lens1_2)))) (PreH34 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1_2) (lens1_2)))) (PreH35 : (PairedPermutation rows rows1_2 lens lens1_2)) (PreH36 : (SameOutsidePairedRange rows rows1_2 lens lens1_2 low_pre high_pre)) (PreH37 : (GreedyPartitionedAt rows1_2 lens1_2 low_pre high_pre pivot)) (PreH38 : ((sum (lens1_2)) = (sum (lens)))) (PreH39 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ (FlatRows flat1_3 rows1 (Zlength (rows1_2)) number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens lens1_3) ” &&
  “ (SameOutsidePairedRange rows rows1 lens lens1_3 low_pre high_pre) ” &&
  “ (GreedySortedRange rows1 lens1_3 low_pre high_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_return_wit_2 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1_2 : (List Int)) (rows2 : (List (List Int))) (lens2 : (List Int)) (flat2 : (List Int)) (PreH1 : (pivot >= high_pre)) (PreH2 : (FlatRows flat2 rows2 count_pre number_width_pre)) (PreH3 : (PairedPermutation rows1_2 rows2 lens1_2 lens2)) (PreH4 : (SameOutsidePairedRange rows1_2 rows2 lens1_2 lens2 low_pre (pivot - 1))) (PreH5 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1))) (PreH6 : (pivot > low_pre)) (PreH7 : ((0 : Int) <= (pivot * number_width_pre))) (PreH8 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH9 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH10 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH11 : (1 <= count_pre)) (PreH12 : (count_pre <= 20)) (PreH13 : (1 <= number_width_pre)) (PreH14 : (number_width_pre <= 10)) (PreH15 : ((0 : Int) <= low_pre)) (PreH16 : (low_pre < high_pre)) (PreH17 : (high_pre < count_pre)) (PreH18 : (low_pre <= pivot)) (PreH19 : (pivot <= high_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : ((Zlength (rows1_2)) = count_pre)) (PreH23 : ((Zlength (lens1_2)) = count_pre)) (PreH24 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1_2)))) (PreH25 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH26 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH27 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1_2) (lens1_2)))) (PreH30 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1_2) (lens1_2)))) (PreH31 : (PairedPermutation rows rows1_2 lens lens1_2)) (PreH32 : (SameOutsidePairedRange rows rows1_2 lens lens1_2 low_pre high_pre)) (PreH33 : (GreedyPartitionedAt rows1_2 lens1_2 low_pre high_pre pivot)) (PreH34 : ((sum (lens1_2)) = (sum (lens)))) (PreH35 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat2)
  ** (intArray.full lengths_pre count_pre lens2)
|--
  EX lens1 : (List Int), EX flat1 : (List Int), EX rows1 : (List (List Int)),
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens lens1) ” &&
  “ (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre) ” &&
  “ (GreedySortedRange rows1 lens1 low_pre high_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1_2 : (List Int)) (rows2 : (List (List Int))) (lens2 : (List Int)) (flat2 : (List Int)) (PreH1 : (pivot >= high_pre)) (PreH2 : (FlatRows flat2 rows2 count_pre number_width_pre)) (PreH3 : (PairedPermutation rows1_2 rows2 lens1_2 lens2)) (PreH4 : (SameOutsidePairedRange rows1_2 rows2 lens1_2 lens2 low_pre (pivot - 1))) (PreH5 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1))) (PreH6 : (pivot > low_pre)) (PreH7 : ((0 : Int) <= (pivot * number_width_pre))) (PreH8 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH9 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH10 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH11 : (1 <= count_pre)) (PreH12 : (count_pre <= 20)) (PreH13 : (1 <= number_width_pre)) (PreH14 : (number_width_pre <= 10)) (PreH15 : ((0 : Int) <= low_pre)) (PreH16 : (low_pre < high_pre)) (PreH17 : (high_pre < count_pre)) (PreH18 : (low_pre <= pivot)) (PreH19 : (pivot <= high_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : ((Zlength (rows1_2)) = count_pre)) (PreH23 : ((Zlength (lens1_2)) = count_pre)) (PreH24 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1_2)))) (PreH25 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH26 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH27 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1_2) (lens1_2)))) (PreH30 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1_2) (lens1_2)))) (PreH31 : (PairedPermutation rows rows1_2 lens lens1_2)) (PreH32 : (SameOutsidePairedRange rows rows1_2 lens lens1_2 low_pre high_pre)) (PreH33 : (GreedyPartitionedAt rows1_2 lens1_2 low_pre high_pre pivot)) (PreH34 : ((sum (lens1_2)) = (sum (lens)))) (PreH35 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ (FlatRows flat2 rows1 (Zlength (rows1_2)) number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens lens2) ” &&
  “ (SameOutsidePairedRange rows rows1 lens lens2 low_pre high_pre) ” &&
  “ (GreedySortedRange rows1 lens2 low_pre high_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_return_wit_3 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1_2 : (List Int)) (lens1_3 : (List Int)) (flat1_3 : (List Int)) (rows1_3 : (List (List Int))) (PreH1 : (FlatRows flat1_3 rows1_3 count_pre number_width_pre)) (PreH2 : (PairedPermutation rows1_2 rows1_3 lens1_2 lens1_3)) (PreH3 : (SameOutsidePairedRange rows1_2 rows1_3 lens1_2 lens1_3 (pivot + 1) high_pre)) (PreH4 : (GreedySortedRange rows1_3 lens1_3 (pivot + 1) high_pre)) (PreH5 : (pivot < high_pre)) (PreH6 : (pivot <= low_pre)) (PreH7 : ((0 : Int) <= (pivot * number_width_pre))) (PreH8 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH9 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH10 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH11 : (1 <= count_pre)) (PreH12 : (count_pre <= 20)) (PreH13 : (1 <= number_width_pre)) (PreH14 : (number_width_pre <= 10)) (PreH15 : ((0 : Int) <= low_pre)) (PreH16 : (low_pre < high_pre)) (PreH17 : (high_pre < count_pre)) (PreH18 : (low_pre <= pivot)) (PreH19 : (pivot <= high_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : ((Zlength (rows1_2)) = count_pre)) (PreH23 : ((Zlength (lens1_2)) = count_pre)) (PreH24 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1_2)))) (PreH25 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH26 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH27 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1_2) (lens1_2)))) (PreH30 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1_2) (lens1_2)))) (PreH31 : (PairedPermutation rows rows1_2 lens lens1_2)) (PreH32 : (SameOutsidePairedRange rows rows1_2 lens lens1_2 low_pre high_pre)) (PreH33 : (GreedyPartitionedAt rows1_2 lens1_2 low_pre high_pre pivot)) (PreH34 : ((sum (lens1_2)) = (sum (lens)))) (PreH35 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1_3)
  ** (intArray.full lengths_pre count_pre lens1_3)
|--
  EX lens1 : (List Int), EX flat1 : (List Int), EX rows1 : (List (List Int)),
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens lens1) ” &&
  “ (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre) ” &&
  “ (GreedySortedRange rows1 lens1 low_pre high_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1_2 : (List (List Int))) (lens1_2 : (List Int)) (flat1_2 : (List Int)) (lens1_3 : (List Int)) (flat1_3 : (List Int)) (rows1_3 : (List (List Int))) (PreH1 : (FlatRows flat1_3 rows1_3 count_pre number_width_pre)) (PreH2 : (PairedPermutation rows1_2 rows1_3 lens1_2 lens1_3)) (PreH3 : (SameOutsidePairedRange rows1_2 rows1_3 lens1_2 lens1_3 (pivot + 1) high_pre)) (PreH4 : (GreedySortedRange rows1_3 lens1_3 (pivot + 1) high_pre)) (PreH5 : (pivot < high_pre)) (PreH6 : (pivot <= low_pre)) (PreH7 : ((0 : Int) <= (pivot * number_width_pre))) (PreH8 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH9 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH10 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH11 : (1 <= count_pre)) (PreH12 : (count_pre <= 20)) (PreH13 : (1 <= number_width_pre)) (PreH14 : (number_width_pre <= 10)) (PreH15 : ((0 : Int) <= low_pre)) (PreH16 : (low_pre < high_pre)) (PreH17 : (high_pre < count_pre)) (PreH18 : (low_pre <= pivot)) (PreH19 : (pivot <= high_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : ((Zlength (rows1_2)) = count_pre)) (PreH23 : ((Zlength (lens1_2)) = count_pre)) (PreH24 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1_2)))) (PreH25 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH26 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH27 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1_2) (lens1_2)))) (PreH30 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1_2) (lens1_2)))) (PreH31 : (PairedPermutation rows rows1_2 lens lens1_2)) (PreH32 : (SameOutsidePairedRange rows rows1_2 lens lens1_2 low_pre high_pre)) (PreH33 : (GreedyPartitionedAt rows1_2 lens1_2 low_pre high_pre pivot)) (PreH34 : ((sum (lens1_2)) = (sum (lens)))) (PreH35 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ (FlatRows flat1_3 rows1 (Zlength (rows1_2)) number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens lens1_3) ” &&
  “ (SameOutsidePairedRange rows rows1 lens lens1_3 low_pre high_pre) ” &&
  “ (GreedySortedRange rows1 lens1_3 low_pre high_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_return_wit_4 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (low_pre >= high_pre)) (PreH2 : ((0 : Int) <= low_pre)) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : ((0 : Int) <= low_pre)) (PreH8 : (low_pre <= count_pre)) (PreH9 : ((-1) <= high_pre)) (PreH10 : (high_pre < count_pre)) (PreH11 : (1 <= (sum (lens)))) (PreH12 : ((sum (lens)) <= 200)) (PreH13 : ((Zlength (rows)) = count_pre)) (PreH14 : ((Zlength (lens)) = count_pre)) (PreH15 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows)))) (PreH16 : (Forall ((LE.le (α := Int)) (1)) lens)) (PreH17 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens)) (PreH18 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH19 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows) (lens)))) (PreH21 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows) (lens)))) (PreH22 : (FlatRows flat rows count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat)
  ** (intArray.full lengths_pre count_pre lens)
|--
  EX lens1 : (List Int), EX flat1 : (List Int), EX rows1 : (List (List Int)),
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens lens1) ” &&
  “ (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre) ” &&
  “ (GreedySortedRange rows1 lens1 low_pre high_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (low_pre >= high_pre)) (PreH2 : ((0 : Int) <= low_pre)) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : ((0 : Int) <= low_pre)) (PreH8 : (low_pre <= count_pre)) (PreH9 : ((-1) <= high_pre)) (PreH10 : (high_pre < count_pre)) (PreH11 : (1 <= (sum (lens)))) (PreH12 : ((sum (lens)) <= 200)) (PreH13 : ((Zlength (rows)) = count_pre)) (PreH14 : ((Zlength (lens)) = count_pre)) (PreH15 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows)))) (PreH16 : (Forall ((LE.le (α := Int)) (1)) lens)) (PreH17 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens)) (PreH18 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH19 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows) (lens)))) (PreH21 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows) (lens)))) (PreH22 : (FlatRows flat rows count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ (FlatRows flat rows1 (Zlength (rows)) number_width_pre) ” &&
  “ (PairedPermutation rows rows1 lens lens) ” &&
  “ (SameOutsidePairedRange rows rows1 lens lens low_pre high_pre) ” &&
  “ (GreedySortedRange rows1 lens low_pre high_pre) ”
  &&  emp
)

noncomputable def quicksort_numbers_partial_solve_wit_1 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (high_pre < count_pre)) (PreH2 : (low_pre < high_pre)) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : ((0 : Int) <= low_pre)) (PreH9 : (low_pre <= count_pre)) (PreH10 : ((-1) <= high_pre)) (PreH11 : (high_pre < count_pre)) (PreH12 : (1 <= (sum (lens)))) (PreH13 : ((sum (lens)) <= 200)) (PreH14 : ((Zlength (rows)) = count_pre)) (PreH15 : ((Zlength (lens)) = count_pre)) (PreH16 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows)))) (PreH17 : (Forall ((LE.le (α := Int)) (1)) lens)) (PreH18 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens)) (PreH19 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH20 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows) (lens)))) (PreH22 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows) (lens)))) (PreH23 : (FlatRows flat rows count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat)
  ** (intArray.full lengths_pre count_pre lens)
|--
  “ (high_pre < count_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre <= count_pre) ” &&
  “ ((-1) <= high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ ((Zlength (rows)) = count_pre) ” &&
  “ ((Zlength (lens)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows) (lens))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows) (lens))) ” &&
  “ (FlatRows flat rows count_pre number_width_pre) ”
  &&  (((lengths_pre + (high_pre * sizeof(INT)))) # Int |-> ((Znth high_pre lens (0 : Int))))
  ** (intArray.missing_i lengths_pre high_pre (0 : Int) count_pre lens)
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat)

noncomputable def quicksort_numbers_partial_solve_wit_2 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (scan : Int) (boundary : Int) (PreH1 : (scan < high_pre)) (PreH2 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH3 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : ((0 : Int) <= low_pre)) (PreH9 : (low_pre < high_pre)) (PreH10 : (high_pre < count_pre)) (PreH11 : ((low_pre - 1) <= boundary)) (PreH12 : (boundary < scan)) (PreH13 : (low_pre <= scan)) (PreH14 : (scan <= high_pre)) (PreH15 : (1 <= (sum (lens)))) (PreH16 : ((sum (lens)) <= 200)) (PreH17 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH18 : (1 <= pivot_length)) (PreH19 : (pivot_length <= number_width_pre)) (PreH20 : ((Zlength (rows1)) = count_pre)) (PreH21 : ((Zlength (lens1)) = count_pre)) (PreH22 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH23 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH24 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH25 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH26 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH27 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH29 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
|--
  “ (scan < high_pre) ” &&
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary < scan) ” &&
  “ (low_pre <= scan) ” &&
  “ (scan <= high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ ((Zlength (rows1)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1))) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (((lengths_pre + (scan * sizeof(INT)))) # Int |-> ((Znth scan lens1 (0 : Int))))
  ** (intArray.missing_i lengths_pre scan (0 : Int) count_pre lens1)
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)

noncomputable def quicksort_numbers_partial_solve_wit_3 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (position : Int) (comparison : Int) (total_length : Int) (current_length : Int) (lens1 : (List Int)) (pivot_length : Int) (boundary : Int) (scan : Int) (PreH1 : (position < current_length)) (PreH2 : (position < total_length)) (PreH3 : ((0 : Int) <= (scan * number_width_pre))) (PreH4 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH5 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH6 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH7 : (1 <= count_pre)) (PreH8 : (count_pre <= 20)) (PreH9 : (1 <= number_width_pre)) (PreH10 : (number_width_pre <= 10)) (PreH11 : ((0 : Int) <= low_pre)) (PreH12 : (low_pre < high_pre)) (PreH13 : (high_pre < count_pre)) (PreH14 : ((low_pre - 1) <= boundary)) (PreH15 : (boundary < scan)) (PreH16 : (low_pre <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (1 <= (sum (lens)))) (PreH19 : ((sum (lens)) <= 200)) (PreH20 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH21 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH22 : (1 <= current_length)) (PreH23 : (current_length <= number_width_pre)) (PreH24 : (1 <= pivot_length)) (PreH25 : (pivot_length <= number_width_pre)) (PreH26 : (total_length = (current_length + pivot_length))) (PreH27 : (comparison = (0 : Int))) (PreH28 : ((0 : Int) <= position)) (PreH29 : (position <= total_length)) (PreH30 : ((Zlength (rows1)) = count_pre)) (PreH31 : ((Zlength (lens1)) = count_pre)) (PreH32 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH34 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH35 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH36 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH38 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH39 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH40 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH41 : ((sum (lens1)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
|--
  “ (position < current_length) ” &&
  “ (position < total_length) ” &&
  “ ((0 : Int) <= (scan * number_width_pre)) ” &&
  “ (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary < scan) ” &&
  “ (low_pre <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (current_length = (Znth (scan) (lens1) ((0 : Int)))) ” &&
  “ (1 <= current_length) ” &&
  “ (current_length <= number_width_pre) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (total_length = (current_length + pivot_length)) ” &&
  “ (comparison = (0 : Int)) ” &&
  “ ((0 : Int) <= position) ” &&
  “ (position <= total_length) ” &&
  “ ((Zlength (rows1)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1))) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1 scan high_pre position) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (((numbers_pre + (((scan * number_width_pre) + position) * sizeof(INT)))) # Int |-> ((Znth ((scan * number_width_pre) + position) flat1 (0 : Int))))
  ** (intArray.missing_i numbers_pre ((scan * number_width_pre) + position) (0 : Int) (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)

noncomputable def quicksort_numbers_partial_solve_wit_4 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (rows1 : (List (List Int))) (position : Int) (comparison : Int) (total_length : Int) (current_length : Int) (lens1 : (List Int)) (pivot_length : Int) (boundary : Int) (scan : Int) (PreH1 : (position >= current_length)) (PreH2 : (position < total_length)) (PreH3 : ((0 : Int) <= (scan * number_width_pre))) (PreH4 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH5 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH6 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH7 : (1 <= count_pre)) (PreH8 : (count_pre <= 20)) (PreH9 : (1 <= number_width_pre)) (PreH10 : (number_width_pre <= 10)) (PreH11 : ((0 : Int) <= low_pre)) (PreH12 : (low_pre < high_pre)) (PreH13 : (high_pre < count_pre)) (PreH14 : ((low_pre - 1) <= boundary)) (PreH15 : (boundary < scan)) (PreH16 : (low_pre <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (1 <= (sum (lens)))) (PreH19 : ((sum (lens)) <= 200)) (PreH20 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH21 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH22 : (1 <= current_length)) (PreH23 : (current_length <= number_width_pre)) (PreH24 : (1 <= pivot_length)) (PreH25 : (pivot_length <= number_width_pre)) (PreH26 : (total_length = (current_length + pivot_length))) (PreH27 : (comparison = (0 : Int))) (PreH28 : ((0 : Int) <= position)) (PreH29 : (position <= total_length)) (PreH30 : ((Zlength (rows1)) = count_pre)) (PreH31 : ((Zlength (lens1)) = count_pre)) (PreH32 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH34 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH35 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH36 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH38 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH39 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH40 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH41 : ((sum (lens1)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
|--
  “ (position >= current_length) ” &&
  “ (position < total_length) ” &&
  “ ((0 : Int) <= (scan * number_width_pre)) ” &&
  “ (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary < scan) ” &&
  “ (low_pre <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (current_length = (Znth (scan) (lens1) ((0 : Int)))) ” &&
  “ (1 <= current_length) ” &&
  “ (current_length <= number_width_pre) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (total_length = (current_length + pivot_length)) ” &&
  “ (comparison = (0 : Int)) ” &&
  “ ((0 : Int) <= position) ” &&
  “ (position <= total_length) ” &&
  “ ((Zlength (rows1)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1))) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1 scan high_pre position) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (((numbers_pre + (((high_pre * number_width_pre) + (position - current_length)) * sizeof(INT)))) # Int |-> ((Znth ((high_pre * number_width_pre) + (position - current_length)) flat1 (0 : Int))))
  ** (intArray.missing_i numbers_pre ((high_pre * number_width_pre) + (position - current_length)) (0 : Int) (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)

noncomputable def quicksort_numbers_partial_solve_wit_5 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (scan : Int) (boundary : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (PreH1 : (position < pivot_length)) (PreH2 : ((0 : Int) <= (scan * number_width_pre))) (PreH3 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH20 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length))) (PreH26 : (comparison = (0 : Int))) (PreH27 : ((0 : Int) <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH30 : ((Zlength (rows1)) = count_pre)) (PreH31 : ((Zlength (lens1)) = count_pre)) (PreH32 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH34 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH35 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH36 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH38 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH39 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH40 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH41 : ((sum (lens1)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
|--
  “ (position < pivot_length) ” &&
  “ ((0 : Int) <= (scan * number_width_pre)) ” &&
  “ (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary < scan) ” &&
  “ (low_pre <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (current_length = (Znth (scan) (lens1) ((0 : Int)))) ” &&
  “ (1 <= current_length) ” &&
  “ (current_length <= number_width_pre) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (total_length = (current_length + pivot_length)) ” &&
  “ (comparison = (0 : Int)) ” &&
  “ ((0 : Int) <= position) ” &&
  “ (position < total_length) ” &&
  “ (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position))) ” &&
  “ ((Zlength (rows1)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1))) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1 scan high_pre position) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (((numbers_pre + (((high_pre * number_width_pre) + position) * sizeof(INT)))) # Int |-> ((Znth ((high_pre * number_width_pre) + position) flat1 (0 : Int))))
  ** (intArray.missing_i numbers_pre ((high_pre * number_width_pre) + position) (0 : Int) (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)

noncomputable def quicksort_numbers_partial_solve_wit_6 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (scan : Int) (boundary : Int) (pivot_length : Int) (current_length : Int) (total_length : Int) (comparison : Int) (position : Int) (left_digit : Int) (PreH1 : (position >= pivot_length)) (PreH2 : ((0 : Int) <= (scan * number_width_pre))) (PreH3 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH20 : (current_length = (Znth (scan) (lens1) ((0 : Int))))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length))) (PreH26 : (comparison = (0 : Int))) (PreH27 : ((0 : Int) <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH30 : ((Zlength (rows1)) = count_pre)) (PreH31 : ((Zlength (lens1)) = count_pre)) (PreH32 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH34 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH35 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH36 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH38 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH39 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan)) (PreH40 : (ConcatComparePrefix rows1 lens1 scan high_pre position)) (PreH41 : ((sum (lens1)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
|--
  “ (position >= pivot_length) ” &&
  “ ((0 : Int) <= (scan * number_width_pre)) ” &&
  “ (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ ((low_pre - 1) <= boundary) ” &&
  “ (boundary < scan) ” &&
  “ (low_pre <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (current_length = (Znth (scan) (lens1) ((0 : Int)))) ” &&
  “ (1 <= current_length) ” &&
  “ (current_length <= number_width_pre) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ (total_length = (current_length + pivot_length)) ” &&
  “ (comparison = (0 : Int)) ” &&
  “ ((0 : Int) <= position) ” &&
  “ (position < total_length) ” &&
  “ (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position))) ” &&
  “ ((Zlength (rows1)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1))) ” &&
  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan) ” &&
  “ (ConcatComparePrefix rows1 lens1 scan high_pre position) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (((numbers_pre + (((scan * number_width_pre) + (position - pivot_length)) * sizeof(INT)))) # Int |-> ((Znth ((scan * number_width_pre) + (position - pivot_length)) flat1 (0 : Int))))
  ** (intArray.missing_i numbers_pre ((scan * number_width_pre) + (position - pivot_length)) (0 : Int) (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)

noncomputable def quicksort_numbers_partial_solve_wit_7 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : (column < number_width_pre)) (PreH2 : ((0 : Int) <= (boundary * number_width_pre))) (PreH3 : (((boundary * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (scan * number_width_pre))) (PreH5 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH7 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : ((0 : Int) <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : ((0 : Int) <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1)) = count_pre)) (PreH27 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before)))) (PreH28 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH29 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH31 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH32 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1)))) (PreH33 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1)))) (PreH34 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH35 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH36 : (comparison > (0 : Int))) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH38 : ((sum (lens1)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
|--
  “ (column < number_width_pre) ” &&
  “ ((0 : Int) <= (boundary * number_width_pre)) ” &&
  “ (((boundary * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (scan * number_width_pre)) ” &&
  “ (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= boundary) ” &&
  “ (boundary <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ ((0 : Int) <= column) ” &&
  “ (column <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ ((Zlength (rows_before)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan) ” &&
  “ (ConcatCompareOutcome rows_before lens1 scan high_pre comparison) ” &&
  “ (comparison > (0 : Int)) ” &&
  “ (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (((numbers_pre + (((boundary * number_width_pre) + column) * sizeof(INT)))) # Int |-> ((Znth ((boundary * number_width_pre) + column) flat_now (0 : Int))))
  ** (intArray.missing_i numbers_pre ((boundary * number_width_pre) + column) (0 : Int) (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)

noncomputable def quicksort_numbers_partial_solve_wit_8 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : (column < number_width_pre)) (PreH2 : ((0 : Int) <= (boundary * number_width_pre))) (PreH3 : (((boundary * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (scan * number_width_pre))) (PreH5 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH7 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : ((0 : Int) <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : ((0 : Int) <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1)) = count_pre)) (PreH27 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before)))) (PreH28 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH29 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH31 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH32 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1)))) (PreH33 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1)))) (PreH34 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH35 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH36 : (comparison > (0 : Int))) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH38 : ((sum (lens1)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
|--
  “ (column < number_width_pre) ” &&
  “ ((0 : Int) <= (boundary * number_width_pre)) ” &&
  “ (((boundary * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (scan * number_width_pre)) ” &&
  “ (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= boundary) ” &&
  “ (boundary <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ ((0 : Int) <= column) ” &&
  “ (column <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ ((Zlength (rows_before)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan) ” &&
  “ (ConcatCompareOutcome rows_before lens1 scan high_pre comparison) ” &&
  “ (comparison > (0 : Int)) ” &&
  “ (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (((numbers_pre + (((scan * number_width_pre) + column) * sizeof(INT)))) # Int |-> ((Znth ((scan * number_width_pre) + column) flat_now (0 : Int))))
  ** (intArray.missing_i numbers_pre ((scan * number_width_pre) + column) (0 : Int) (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)

noncomputable def quicksort_numbers_partial_solve_wit_9 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : (column < number_width_pre)) (PreH2 : ((0 : Int) <= (boundary * number_width_pre))) (PreH3 : (((boundary * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (scan * number_width_pre))) (PreH5 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH7 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : ((0 : Int) <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : ((0 : Int) <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1)) = count_pre)) (PreH27 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before)))) (PreH28 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH29 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH31 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH32 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1)))) (PreH33 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1)))) (PreH34 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH35 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH36 : (comparison > (0 : Int))) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH38 : ((sum (lens1)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
|--
  “ (column < number_width_pre) ” &&
  “ ((0 : Int) <= (boundary * number_width_pre)) ” &&
  “ (((boundary * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (scan * number_width_pre)) ” &&
  “ (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= boundary) ” &&
  “ (boundary <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ ((0 : Int) <= column) ” &&
  “ (column <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ ((Zlength (rows_before)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan) ” &&
  “ (ConcatCompareOutcome rows_before lens1 scan high_pre comparison) ” &&
  “ (comparison > (0 : Int)) ” &&
  “ (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (((numbers_pre + (((boundary * number_width_pre) + column) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i numbers_pre ((boundary * number_width_pre) + column) (0 : Int) (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)

noncomputable def quicksort_numbers_partial_solve_wit_10 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : (column < number_width_pre)) (PreH2 : ((0 : Int) <= (boundary * number_width_pre))) (PreH3 : (((boundary * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (scan * number_width_pre))) (PreH5 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH7 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : ((0 : Int) <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : ((0 : Int) <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1)) = count_pre)) (PreH27 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before)))) (PreH28 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH29 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH31 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH32 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1)))) (PreH33 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1)))) (PreH34 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH35 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH36 : (comparison > (0 : Int))) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH38 : ((sum (lens1)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) (replace_Znth (((boundary * number_width_pre) + column)) ((Znth ((scan * number_width_pre) + column) flat_now (0 : Int))) (flat_now)))
  ** (intArray.full lengths_pre count_pre lens1)
|--
  “ (column < number_width_pre) ” &&
  “ ((0 : Int) <= (boundary * number_width_pre)) ” &&
  “ (((boundary * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (scan * number_width_pre)) ” &&
  “ (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= boundary) ” &&
  “ (boundary <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ ((0 : Int) <= column) ” &&
  “ (column <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ ((Zlength (rows_before)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan) ” &&
  “ (ConcatCompareOutcome rows_before lens1 scan high_pre comparison) ” &&
  “ (comparison > (0 : Int)) ” &&
  “ (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (((numbers_pre + (((scan * number_width_pre) + column) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i numbers_pre ((scan * number_width_pre) + column) (0 : Int) (count_pre * number_width_pre) (replace_Znth (((boundary * number_width_pre) + column)) ((Znth ((scan * number_width_pre) + column) flat_now (0 : Int))) (flat_now)))
  ** (intArray.full lengths_pre count_pre lens1)

noncomputable def quicksort_numbers_partial_solve_wit_11 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : (column >= number_width_pre)) (PreH2 : ((0 : Int) <= (boundary * number_width_pre))) (PreH3 : (((boundary * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (scan * number_width_pre))) (PreH5 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH7 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : ((0 : Int) <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : ((0 : Int) <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1)) = count_pre)) (PreH27 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before)))) (PreH28 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH29 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH31 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH32 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1)))) (PreH33 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1)))) (PreH34 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH35 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH36 : (comparison > (0 : Int))) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH38 : ((sum (lens1)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
|--
  “ (column >= number_width_pre) ” &&
  “ ((0 : Int) <= (boundary * number_width_pre)) ” &&
  “ (((boundary * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (scan * number_width_pre)) ” &&
  “ (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= boundary) ” &&
  “ (boundary <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ ((0 : Int) <= column) ” &&
  “ (column <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ ((Zlength (rows_before)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan) ” &&
  “ (ConcatCompareOutcome rows_before lens1 scan high_pre comparison) ” &&
  “ (comparison > (0 : Int)) ” &&
  “ (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (((lengths_pre + (boundary * sizeof(INT)))) # Int |-> ((Znth boundary lens1 (0 : Int))))
  ** (intArray.missing_i lengths_pre boundary (0 : Int) count_pre lens1)
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)

noncomputable def quicksort_numbers_partial_solve_wit_12 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : (column >= number_width_pre)) (PreH2 : ((0 : Int) <= (boundary * number_width_pre))) (PreH3 : (((boundary * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (scan * number_width_pre))) (PreH5 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH7 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : ((0 : Int) <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : ((0 : Int) <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1)) = count_pre)) (PreH27 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before)))) (PreH28 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH29 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH31 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH32 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1)))) (PreH33 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1)))) (PreH34 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH35 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH36 : (comparison > (0 : Int))) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH38 : ((sum (lens1)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full lengths_pre count_pre lens1)
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
|--
  “ (column >= number_width_pre) ” &&
  “ ((0 : Int) <= (boundary * number_width_pre)) ” &&
  “ (((boundary * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (scan * number_width_pre)) ” &&
  “ (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= boundary) ” &&
  “ (boundary <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ ((0 : Int) <= column) ” &&
  “ (column <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ ((Zlength (rows_before)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan) ” &&
  “ (ConcatCompareOutcome rows_before lens1 scan high_pre comparison) ” &&
  “ (comparison > (0 : Int)) ” &&
  “ (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (((lengths_pre + (scan * sizeof(INT)))) # Int |-> ((Znth scan lens1 (0 : Int))))
  ** (intArray.missing_i lengths_pre scan (0 : Int) count_pre lens1)
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)

noncomputable def quicksort_numbers_partial_solve_wit_13 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : (column >= number_width_pre)) (PreH2 : ((0 : Int) <= (boundary * number_width_pre))) (PreH3 : (((boundary * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (scan * number_width_pre))) (PreH5 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH7 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : ((0 : Int) <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : ((0 : Int) <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1)) = count_pre)) (PreH27 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before)))) (PreH28 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH29 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH31 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH32 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1)))) (PreH33 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1)))) (PreH34 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH35 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH36 : (comparison > (0 : Int))) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH38 : ((sum (lens1)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full lengths_pre count_pre lens1)
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
|--
  “ (column >= number_width_pre) ” &&
  “ ((0 : Int) <= (boundary * number_width_pre)) ” &&
  “ (((boundary * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (scan * number_width_pre)) ” &&
  “ (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= boundary) ” &&
  “ (boundary <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ ((0 : Int) <= column) ” &&
  “ (column <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ ((Zlength (rows_before)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan) ” &&
  “ (ConcatCompareOutcome rows_before lens1 scan high_pre comparison) ” &&
  “ (comparison > (0 : Int)) ” &&
  “ (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (((lengths_pre + (boundary * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i lengths_pre boundary (0 : Int) count_pre lens1)
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)

noncomputable def quicksort_numbers_partial_solve_wit_14 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (comparison : Int) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (scan : Int) (boundary : Int) (PreH1 : (column >= number_width_pre)) (PreH2 : ((0 : Int) <= (boundary * number_width_pre))) (PreH3 : (((boundary * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (scan * number_width_pre))) (PreH5 : (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH7 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : ((0 : Int) <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : ((0 : Int) <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1)) = count_pre)) (PreH27 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before)))) (PreH28 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH29 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH31 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH32 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1)))) (PreH33 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1)))) (PreH34 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan)) (PreH35 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison)) (PreH36 : (comparison > (0 : Int))) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre)) (PreH38 : ((sum (lens1)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full lengths_pre count_pre (replace_Znth (boundary) ((Znth scan lens1 (0 : Int))) (lens1)))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
|--
  “ (column >= number_width_pre) ” &&
  “ ((0 : Int) <= (boundary * number_width_pre)) ” &&
  “ (((boundary * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (scan * number_width_pre)) ” &&
  “ (((scan * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= boundary) ” &&
  “ (boundary <= scan) ” &&
  “ (scan < high_pre) ” &&
  “ ((0 : Int) <= column) ” &&
  “ (column <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ ((Zlength (rows_before)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1) scan) ” &&
  “ (ConcatCompareOutcome rows_before lens1 scan high_pre comparison) ” &&
  “ (comparison > (0 : Int)) ” &&
  “ (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (((lengths_pre + (scan * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i lengths_pre scan (0 : Int) count_pre (replace_Znth (boundary) ((Znth scan lens1 (0 : Int))) (lens1)))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)

noncomputable def quicksort_numbers_partial_solve_wit_15 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : (column < number_width_pre)) (PreH2 : ((0 : Int) <= (pivot * number_width_pre))) (PreH3 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : ((0 : Int) <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before)))) (PreH25 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH26 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH27 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1)))) (PreH30 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1)))) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
|--
  “ (column < number_width_pre) ” &&
  “ ((0 : Int) <= (pivot * number_width_pre)) ” &&
  “ (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= pivot) ” &&
  “ (pivot <= high_pre) ” &&
  “ ((0 : Int) <= column) ” &&
  “ (column <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ ((Zlength (rows_before)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre) ” &&
  “ (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (((numbers_pre + (((pivot * number_width_pre) + column) * sizeof(INT)))) # Int |-> ((Znth ((pivot * number_width_pre) + column) flat_now (0 : Int))))
  ** (intArray.missing_i numbers_pre ((pivot * number_width_pre) + column) (0 : Int) (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)

noncomputable def quicksort_numbers_partial_solve_wit_16 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : (column < number_width_pre)) (PreH2 : ((0 : Int) <= (pivot * number_width_pre))) (PreH3 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : ((0 : Int) <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before)))) (PreH25 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH26 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH27 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1)))) (PreH30 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1)))) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
|--
  “ (column < number_width_pre) ” &&
  “ ((0 : Int) <= (pivot * number_width_pre)) ” &&
  “ (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= pivot) ” &&
  “ (pivot <= high_pre) ” &&
  “ ((0 : Int) <= column) ” &&
  “ (column <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ ((Zlength (rows_before)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre) ” &&
  “ (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (((numbers_pre + (((high_pre * number_width_pre) + column) * sizeof(INT)))) # Int |-> ((Znth ((high_pre * number_width_pre) + column) flat_now (0 : Int))))
  ** (intArray.missing_i numbers_pre ((high_pre * number_width_pre) + column) (0 : Int) (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)

noncomputable def quicksort_numbers_partial_solve_wit_17 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : (column < number_width_pre)) (PreH2 : ((0 : Int) <= (pivot * number_width_pre))) (PreH3 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : ((0 : Int) <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before)))) (PreH25 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH26 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH27 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1)))) (PreH30 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1)))) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
|--
  “ (column < number_width_pre) ” &&
  “ ((0 : Int) <= (pivot * number_width_pre)) ” &&
  “ (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= pivot) ” &&
  “ (pivot <= high_pre) ” &&
  “ ((0 : Int) <= column) ” &&
  “ (column <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ ((Zlength (rows_before)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre) ” &&
  “ (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (((numbers_pre + (((pivot * number_width_pre) + column) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i numbers_pre ((pivot * number_width_pre) + column) (0 : Int) (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)

noncomputable def quicksort_numbers_partial_solve_wit_18 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : (column < number_width_pre)) (PreH2 : ((0 : Int) <= (pivot * number_width_pre))) (PreH3 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : ((0 : Int) <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before)))) (PreH25 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH26 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH27 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1)))) (PreH30 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1)))) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) (replace_Znth (((pivot * number_width_pre) + column)) ((Znth ((high_pre * number_width_pre) + column) flat_now (0 : Int))) (flat_now)))
  ** (intArray.full lengths_pre count_pre lens1)
|--
  “ (column < number_width_pre) ” &&
  “ ((0 : Int) <= (pivot * number_width_pre)) ” &&
  “ (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= pivot) ” &&
  “ (pivot <= high_pre) ” &&
  “ ((0 : Int) <= column) ” &&
  “ (column <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ ((Zlength (rows_before)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre) ” &&
  “ (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (((numbers_pre + (((high_pre * number_width_pre) + column) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i numbers_pre ((high_pre * number_width_pre) + column) (0 : Int) (count_pre * number_width_pre) (replace_Znth (((pivot * number_width_pre) + column)) ((Znth ((high_pre * number_width_pre) + column) flat_now (0 : Int))) (flat_now)))
  ** (intArray.full lengths_pre count_pre lens1)

noncomputable def quicksort_numbers_partial_solve_wit_19 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : (column >= number_width_pre)) (PreH2 : ((0 : Int) <= (pivot * number_width_pre))) (PreH3 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : ((0 : Int) <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before)))) (PreH25 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH26 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH27 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1)))) (PreH30 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1)))) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
  ** (intArray.full lengths_pre count_pre lens1)
|--
  “ (column >= number_width_pre) ” &&
  “ ((0 : Int) <= (pivot * number_width_pre)) ” &&
  “ (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= pivot) ” &&
  “ (pivot <= high_pre) ” &&
  “ ((0 : Int) <= column) ” &&
  “ (column <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ ((Zlength (rows_before)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre) ” &&
  “ (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (((lengths_pre + (pivot * sizeof(INT)))) # Int |-> ((Znth pivot lens1 (0 : Int))))
  ** (intArray.missing_i lengths_pre pivot (0 : Int) count_pre lens1)
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)

noncomputable def quicksort_numbers_partial_solve_wit_20 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : (column >= number_width_pre)) (PreH2 : ((0 : Int) <= (pivot * number_width_pre))) (PreH3 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : ((0 : Int) <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before)))) (PreH25 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH26 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH27 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1)))) (PreH30 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1)))) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full lengths_pre count_pre lens1)
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
|--
  “ (column >= number_width_pre) ” &&
  “ ((0 : Int) <= (pivot * number_width_pre)) ” &&
  “ (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= pivot) ” &&
  “ (pivot <= high_pre) ” &&
  “ ((0 : Int) <= column) ” &&
  “ (column <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ ((Zlength (rows_before)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre) ” &&
  “ (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (((lengths_pre + (high_pre * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i lengths_pre high_pre (0 : Int) count_pre lens1)
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)

noncomputable def quicksort_numbers_partial_solve_wit_21 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat_now : (List Int)) (rows_now : (List (List Int))) (rows_before : (List (List Int))) (lens1 : (List Int)) (pivot_length : Int) (column : Int) (pivot : Int) (PreH1 : (column >= number_width_pre)) (PreH2 : ((0 : Int) <= (pivot * number_width_pre))) (PreH3 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : ((0 : Int) <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) ((0 : Int))))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before)))) (PreH25 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH26 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH27 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before)))) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1)))) (PreH30 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1)))) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre)) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre)) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre)) ,
  (intArray.full lengths_pre count_pre (replace_Znth (high_pre) ((Znth pivot lens1 (0 : Int))) (lens1)))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)
|--
  “ (column >= number_width_pre) ” &&
  “ ((0 : Int) <= (pivot * number_width_pre)) ” &&
  “ (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= pivot) ” &&
  “ (pivot <= high_pre) ” &&
  “ ((0 : Int) <= column) ” &&
  “ (column <= number_width_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ (pivot_length = (Znth (high_pre) (lens1) ((0 : Int)))) ” &&
  “ (1 <= pivot_length) ” &&
  “ (pivot_length <= number_width_pre) ” &&
  “ ((Zlength (rows_before)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows_before))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows_before) (lens1))) ” &&
  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1) high_pre) ” &&
  “ (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat_now rows_now count_pre number_width_pre) ”
  &&  (((lengths_pre + (pivot * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i lengths_pre pivot (0 : Int) count_pre (replace_Znth (high_pre) ((Znth pivot lens1 (0 : Int))) (lens1)))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat_now)

noncomputable def quicksort_numbers_partial_solve_wit_22_pure : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (PreH1 : (pivot > low_pre)) (PreH2 : ((0 : Int) <= (pivot * number_width_pre))) (PreH3 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : (1 <= (sum (lens)))) (PreH16 : ((sum (lens)) <= 200)) (PreH17 : ((Zlength (rows1)) = count_pre)) (PreH18 : ((Zlength (lens1)) = count_pre)) (PreH19 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH20 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH21 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH23 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH24 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH25 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH26 : (PairedPermutation rows rows1 lens lens1)) (PreH27 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH28 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH29 : ((sum (lens1)) = (sum (lens)))) (PreH30 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
  ** ((( &( "pivot_length" ) )) # Int |->_)
|--
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre <= count_pre) ” &&
  “ ((-1) <= (pivot - 1)) ” &&
  “ ((pivot - 1) < count_pre) ” &&
  “ (1 <= (sum (lens1))) ” &&
  “ ((sum (lens1)) <= 200) ” &&
  “ ((Zlength (rows1)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”

noncomputable def quicksort_numbers_partial_solve_wit_22_aux : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (PreH1 : (pivot > low_pre)) (PreH2 : ((0 : Int) <= (pivot * number_width_pre))) (PreH3 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH5 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : ((0 : Int) <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : (1 <= (sum (lens)))) (PreH16 : ((sum (lens)) <= 200)) (PreH17 : ((Zlength (rows1)) = count_pre)) (PreH18 : ((Zlength (lens1)) = count_pre)) (PreH19 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH20 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH21 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH23 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH24 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH25 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH26 : (PairedPermutation rows rows1 lens lens1)) (PreH27 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH28 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH29 : ((sum (lens1)) = (sum (lens)))) (PreH30 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
|--
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre <= count_pre) ” &&
  “ ((-1) <= (pivot - 1)) ” &&
  “ ((pivot - 1) < count_pre) ” &&
  “ (1 <= (sum (lens1))) ” &&
  “ ((sum (lens1)) <= 200) ” &&
  “ ((Zlength (rows1)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ” &&
  “ (pivot > low_pre) ” &&
  “ ((0 : Int) <= (pivot * number_width_pre)) ” &&
  “ (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= pivot) ” &&
  “ (pivot <= high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ ((Zlength (rows1)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1))) ” &&
  “ (PairedPermutation rows rows1 lens lens1) ” &&
  “ (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre) ” &&
  “ (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)

noncomputable def quicksort_numbers_partial_solve_wit_22 : Prop := quicksort_numbers_partial_solve_wit_22_pure -> quicksort_numbers_partial_solve_wit_22_aux

noncomputable def quicksort_numbers_partial_solve_wit_23_pure : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (rows2 : (List (List Int))) (lens2 : (List Int)) (flat2 : (List Int)) (PreH1 : (pivot < high_pre)) (PreH2 : (FlatRows flat2 rows2 count_pre number_width_pre)) (PreH3 : (PairedPermutation rows1 rows2 lens1 lens2)) (PreH4 : (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1))) (PreH5 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1))) (PreH6 : (pivot > low_pre)) (PreH7 : ((0 : Int) <= (pivot * number_width_pre))) (PreH8 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH9 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH10 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH11 : (1 <= count_pre)) (PreH12 : (count_pre <= 20)) (PreH13 : (1 <= number_width_pre)) (PreH14 : (number_width_pre <= 10)) (PreH15 : ((0 : Int) <= low_pre)) (PreH16 : (low_pre < high_pre)) (PreH17 : (high_pre < count_pre)) (PreH18 : (low_pre <= pivot)) (PreH19 : (pivot <= high_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : ((Zlength (rows1)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH25 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH26 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH27 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH30 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH31 : (PairedPermutation rows rows1 lens lens1)) (PreH32 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH33 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH34 : ((sum (lens1)) = (sum (lens)))) (PreH35 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat2)
  ** (intArray.full lengths_pre count_pre lens2)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
  ** ((( &( "pivot_length" ) )) # Int |->_)
|--
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= (pivot + 1)) ” &&
  “ ((pivot + 1) <= count_pre) ” &&
  “ ((-1) <= high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (FlatRows flat2 rows2 count_pre number_width_pre) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows2) (lens2))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows2) (lens2))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows2))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows2))) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens2) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens2) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows2))) ” &&
  “ ((Zlength (lens2)) = count_pre) ” &&
  “ ((Zlength (rows2)) = count_pre) ” &&
  “ ((sum (lens2)) <= 200) ” &&
  “ (1 <= (sum (lens2))) ”
) \/
(
forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (rows2 : (List (List Int))) (lens2 : (List Int)) (flat2 : (List Int)) (PreH1 : (pivot <= INT_MAX)) (PreH2 : (high_pre <= INT_MAX)) (PreH3 : (low_pre <= INT_MAX)) (PreH4 : (number_width_pre <= INT_MAX)) (PreH5 : (count_pre <= INT_MAX)) (PreH6 : (pivot >= INT_MIN)) (PreH7 : (high_pre >= INT_MIN)) (PreH8 : (low_pre >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (count_pre >= INT_MIN)) (PreH11 : (pivot < high_pre)) (PreH12 : (FlatRows flat2 rows2 count_pre number_width_pre)) (PreH13 : (PairedPermutation rows1 rows2 lens1 lens2)) (PreH14 : (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1))) (PreH15 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1))) (PreH16 : (pivot > low_pre)) (PreH17 : ((0 : Int) <= (pivot * number_width_pre))) (PreH18 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH19 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH20 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH21 : (1 <= count_pre)) (PreH22 : (count_pre <= 20)) (PreH23 : (1 <= number_width_pre)) (PreH24 : (number_width_pre <= 10)) (PreH25 : ((0 : Int) <= low_pre)) (PreH26 : (low_pre < high_pre)) (PreH27 : (high_pre < count_pre)) (PreH28 : (low_pre <= pivot)) (PreH29 : (pivot <= high_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : ((Zlength (rows1)) = count_pre)) (PreH33 : ((Zlength (lens1)) = count_pre)) (PreH34 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH35 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH36 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH37 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH38 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH39 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH40 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH41 : (PairedPermutation rows rows1 lens lens1)) (PreH42 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH43 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH44 : ((sum (lens1)) = (sum (lens)))) (PreH45 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat2)
  ** (intArray.full lengths_pre count_pre lens2)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
  ** ((( &( "pivot_length" ) )) # Int |->_)
|--
  “ (1 <= (sum (lens2))) ” &&
  “ ((sum (lens2)) <= 200) ” &&
  “ ((Zlength (rows2)) = count_pre) ” &&
  “ ((Zlength (lens2)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows2))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens2) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens2) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows2))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows2))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows2) (lens2))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows2) (lens2))) ”
)

noncomputable def quicksort_numbers_partial_solve_wit_23_pure_split_goal_1 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (rows2 : (List (List Int))) (lens2 : (List Int)) (flat2 : (List Int)) (PreH1 : (pivot <= INT_MAX)) (PreH2 : (high_pre <= INT_MAX)) (PreH3 : (low_pre <= INT_MAX)) (PreH4 : (number_width_pre <= INT_MAX)) (PreH5 : (count_pre <= INT_MAX)) (PreH6 : (pivot >= INT_MIN)) (PreH7 : (high_pre >= INT_MIN)) (PreH8 : (low_pre >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (count_pre >= INT_MIN)) (PreH11 : (pivot < high_pre)) (PreH12 : (FlatRows flat2 rows2 count_pre number_width_pre)) (PreH13 : (PairedPermutation rows1 rows2 lens1 lens2)) (PreH14 : (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1))) (PreH15 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1))) (PreH16 : (pivot > low_pre)) (PreH17 : ((0 : Int) <= (pivot * number_width_pre))) (PreH18 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH19 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH20 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH21 : (1 <= count_pre)) (PreH22 : (count_pre <= 20)) (PreH23 : (1 <= number_width_pre)) (PreH24 : (number_width_pre <= 10)) (PreH25 : ((0 : Int) <= low_pre)) (PreH26 : (low_pre < high_pre)) (PreH27 : (high_pre < count_pre)) (PreH28 : (low_pre <= pivot)) (PreH29 : (pivot <= high_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : ((Zlength (rows1)) = count_pre)) (PreH33 : ((Zlength (lens1)) = count_pre)) (PreH34 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH35 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH36 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH37 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH38 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH39 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH40 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH41 : (PairedPermutation rows rows1 lens lens1)) (PreH42 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH43 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH44 : ((sum (lens1)) = (sum (lens)))) (PreH45 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat2)
  ** (intArray.full lengths_pre count_pre lens2)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
  ** ((( &( "pivot_length" ) )) # Int |->_)
|--
  “ (1 <= (sum (lens2))) ”

noncomputable def quicksort_numbers_partial_solve_wit_23_pure_split_goal_2 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (rows2 : (List (List Int))) (lens2 : (List Int)) (flat2 : (List Int)) (PreH1 : (pivot <= INT_MAX)) (PreH2 : (high_pre <= INT_MAX)) (PreH3 : (low_pre <= INT_MAX)) (PreH4 : (number_width_pre <= INT_MAX)) (PreH5 : (count_pre <= INT_MAX)) (PreH6 : (pivot >= INT_MIN)) (PreH7 : (high_pre >= INT_MIN)) (PreH8 : (low_pre >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (count_pre >= INT_MIN)) (PreH11 : (pivot < high_pre)) (PreH12 : (FlatRows flat2 rows2 count_pre number_width_pre)) (PreH13 : (PairedPermutation rows1 rows2 lens1 lens2)) (PreH14 : (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1))) (PreH15 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1))) (PreH16 : (pivot > low_pre)) (PreH17 : ((0 : Int) <= (pivot * number_width_pre))) (PreH18 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH19 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH20 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH21 : (1 <= count_pre)) (PreH22 : (count_pre <= 20)) (PreH23 : (1 <= number_width_pre)) (PreH24 : (number_width_pre <= 10)) (PreH25 : ((0 : Int) <= low_pre)) (PreH26 : (low_pre < high_pre)) (PreH27 : (high_pre < count_pre)) (PreH28 : (low_pre <= pivot)) (PreH29 : (pivot <= high_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : ((Zlength (rows1)) = count_pre)) (PreH33 : ((Zlength (lens1)) = count_pre)) (PreH34 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH35 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH36 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH37 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH38 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH39 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH40 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH41 : (PairedPermutation rows rows1 lens lens1)) (PreH42 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH43 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH44 : ((sum (lens1)) = (sum (lens)))) (PreH45 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat2)
  ** (intArray.full lengths_pre count_pre lens2)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
  ** ((( &( "pivot_length" ) )) # Int |->_)
|--
  “ ((sum (lens2)) <= 200) ”

noncomputable def quicksort_numbers_partial_solve_wit_23_pure_split_goal_3 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (rows2 : (List (List Int))) (lens2 : (List Int)) (flat2 : (List Int)) (PreH1 : (pivot <= INT_MAX)) (PreH2 : (high_pre <= INT_MAX)) (PreH3 : (low_pre <= INT_MAX)) (PreH4 : (number_width_pre <= INT_MAX)) (PreH5 : (count_pre <= INT_MAX)) (PreH6 : (pivot >= INT_MIN)) (PreH7 : (high_pre >= INT_MIN)) (PreH8 : (low_pre >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (count_pre >= INT_MIN)) (PreH11 : (pivot < high_pre)) (PreH12 : (FlatRows flat2 rows2 count_pre number_width_pre)) (PreH13 : (PairedPermutation rows1 rows2 lens1 lens2)) (PreH14 : (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1))) (PreH15 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1))) (PreH16 : (pivot > low_pre)) (PreH17 : ((0 : Int) <= (pivot * number_width_pre))) (PreH18 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH19 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH20 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH21 : (1 <= count_pre)) (PreH22 : (count_pre <= 20)) (PreH23 : (1 <= number_width_pre)) (PreH24 : (number_width_pre <= 10)) (PreH25 : ((0 : Int) <= low_pre)) (PreH26 : (low_pre < high_pre)) (PreH27 : (high_pre < count_pre)) (PreH28 : (low_pre <= pivot)) (PreH29 : (pivot <= high_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : ((Zlength (rows1)) = count_pre)) (PreH33 : ((Zlength (lens1)) = count_pre)) (PreH34 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH35 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH36 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH37 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH38 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH39 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH40 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH41 : (PairedPermutation rows rows1 lens lens1)) (PreH42 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH43 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH44 : ((sum (lens1)) = (sum (lens)))) (PreH45 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat2)
  ** (intArray.full lengths_pre count_pre lens2)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
  ** ((( &( "pivot_length" ) )) # Int |->_)
|--
  “ ((Zlength (rows2)) = count_pre) ”

noncomputable def quicksort_numbers_partial_solve_wit_23_pure_split_goal_4 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (rows2 : (List (List Int))) (lens2 : (List Int)) (flat2 : (List Int)) (PreH1 : (pivot <= INT_MAX)) (PreH2 : (high_pre <= INT_MAX)) (PreH3 : (low_pre <= INT_MAX)) (PreH4 : (number_width_pre <= INT_MAX)) (PreH5 : (count_pre <= INT_MAX)) (PreH6 : (pivot >= INT_MIN)) (PreH7 : (high_pre >= INT_MIN)) (PreH8 : (low_pre >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (count_pre >= INT_MIN)) (PreH11 : (pivot < high_pre)) (PreH12 : (FlatRows flat2 rows2 count_pre number_width_pre)) (PreH13 : (PairedPermutation rows1 rows2 lens1 lens2)) (PreH14 : (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1))) (PreH15 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1))) (PreH16 : (pivot > low_pre)) (PreH17 : ((0 : Int) <= (pivot * number_width_pre))) (PreH18 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH19 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH20 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH21 : (1 <= count_pre)) (PreH22 : (count_pre <= 20)) (PreH23 : (1 <= number_width_pre)) (PreH24 : (number_width_pre <= 10)) (PreH25 : ((0 : Int) <= low_pre)) (PreH26 : (low_pre < high_pre)) (PreH27 : (high_pre < count_pre)) (PreH28 : (low_pre <= pivot)) (PreH29 : (pivot <= high_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : ((Zlength (rows1)) = count_pre)) (PreH33 : ((Zlength (lens1)) = count_pre)) (PreH34 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH35 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH36 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH37 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH38 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH39 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH40 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH41 : (PairedPermutation rows rows1 lens lens1)) (PreH42 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH43 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH44 : ((sum (lens1)) = (sum (lens)))) (PreH45 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat2)
  ** (intArray.full lengths_pre count_pre lens2)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
  ** ((( &( "pivot_length" ) )) # Int |->_)
|--
  “ ((Zlength (lens2)) = count_pre) ”

noncomputable def quicksort_numbers_partial_solve_wit_23_pure_split_goal_5 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (rows2 : (List (List Int))) (lens2 : (List Int)) (flat2 : (List Int)) (PreH1 : (pivot <= INT_MAX)) (PreH2 : (high_pre <= INT_MAX)) (PreH3 : (low_pre <= INT_MAX)) (PreH4 : (number_width_pre <= INT_MAX)) (PreH5 : (count_pre <= INT_MAX)) (PreH6 : (pivot >= INT_MIN)) (PreH7 : (high_pre >= INT_MIN)) (PreH8 : (low_pre >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (count_pre >= INT_MIN)) (PreH11 : (pivot < high_pre)) (PreH12 : (FlatRows flat2 rows2 count_pre number_width_pre)) (PreH13 : (PairedPermutation rows1 rows2 lens1 lens2)) (PreH14 : (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1))) (PreH15 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1))) (PreH16 : (pivot > low_pre)) (PreH17 : ((0 : Int) <= (pivot * number_width_pre))) (PreH18 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH19 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH20 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH21 : (1 <= count_pre)) (PreH22 : (count_pre <= 20)) (PreH23 : (1 <= number_width_pre)) (PreH24 : (number_width_pre <= 10)) (PreH25 : ((0 : Int) <= low_pre)) (PreH26 : (low_pre < high_pre)) (PreH27 : (high_pre < count_pre)) (PreH28 : (low_pre <= pivot)) (PreH29 : (pivot <= high_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : ((Zlength (rows1)) = count_pre)) (PreH33 : ((Zlength (lens1)) = count_pre)) (PreH34 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH35 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH36 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH37 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH38 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH39 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH40 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH41 : (PairedPermutation rows rows1 lens lens1)) (PreH42 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH43 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH44 : ((sum (lens1)) = (sum (lens)))) (PreH45 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat2)
  ** (intArray.full lengths_pre count_pre lens2)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
  ** ((( &( "pivot_length" ) )) # Int |->_)
|--
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows2))) ”

noncomputable def quicksort_numbers_partial_solve_wit_23_pure_split_goal_6 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (rows2 : (List (List Int))) (lens2 : (List Int)) (flat2 : (List Int)) (PreH1 : (pivot <= INT_MAX)) (PreH2 : (high_pre <= INT_MAX)) (PreH3 : (low_pre <= INT_MAX)) (PreH4 : (number_width_pre <= INT_MAX)) (PreH5 : (count_pre <= INT_MAX)) (PreH6 : (pivot >= INT_MIN)) (PreH7 : (high_pre >= INT_MIN)) (PreH8 : (low_pre >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (count_pre >= INT_MIN)) (PreH11 : (pivot < high_pre)) (PreH12 : (FlatRows flat2 rows2 count_pre number_width_pre)) (PreH13 : (PairedPermutation rows1 rows2 lens1 lens2)) (PreH14 : (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1))) (PreH15 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1))) (PreH16 : (pivot > low_pre)) (PreH17 : ((0 : Int) <= (pivot * number_width_pre))) (PreH18 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH19 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH20 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH21 : (1 <= count_pre)) (PreH22 : (count_pre <= 20)) (PreH23 : (1 <= number_width_pre)) (PreH24 : (number_width_pre <= 10)) (PreH25 : ((0 : Int) <= low_pre)) (PreH26 : (low_pre < high_pre)) (PreH27 : (high_pre < count_pre)) (PreH28 : (low_pre <= pivot)) (PreH29 : (pivot <= high_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : ((Zlength (rows1)) = count_pre)) (PreH33 : ((Zlength (lens1)) = count_pre)) (PreH34 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH35 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH36 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH37 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH38 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH39 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH40 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH41 : (PairedPermutation rows rows1 lens lens1)) (PreH42 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH43 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH44 : ((sum (lens1)) = (sum (lens)))) (PreH45 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat2)
  ** (intArray.full lengths_pre count_pre lens2)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
  ** ((( &( "pivot_length" ) )) # Int |->_)
|--
  “ (Forall ((LE.le (α := Int)) (1)) lens2) ”

noncomputable def quicksort_numbers_partial_solve_wit_23_pure_split_goal_7 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (rows2 : (List (List Int))) (lens2 : (List Int)) (flat2 : (List Int)) (PreH1 : (pivot <= INT_MAX)) (PreH2 : (high_pre <= INT_MAX)) (PreH3 : (low_pre <= INT_MAX)) (PreH4 : (number_width_pre <= INT_MAX)) (PreH5 : (count_pre <= INT_MAX)) (PreH6 : (pivot >= INT_MIN)) (PreH7 : (high_pre >= INT_MIN)) (PreH8 : (low_pre >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (count_pre >= INT_MIN)) (PreH11 : (pivot < high_pre)) (PreH12 : (FlatRows flat2 rows2 count_pre number_width_pre)) (PreH13 : (PairedPermutation rows1 rows2 lens1 lens2)) (PreH14 : (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1))) (PreH15 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1))) (PreH16 : (pivot > low_pre)) (PreH17 : ((0 : Int) <= (pivot * number_width_pre))) (PreH18 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH19 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH20 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH21 : (1 <= count_pre)) (PreH22 : (count_pre <= 20)) (PreH23 : (1 <= number_width_pre)) (PreH24 : (number_width_pre <= 10)) (PreH25 : ((0 : Int) <= low_pre)) (PreH26 : (low_pre < high_pre)) (PreH27 : (high_pre < count_pre)) (PreH28 : (low_pre <= pivot)) (PreH29 : (pivot <= high_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : ((Zlength (rows1)) = count_pre)) (PreH33 : ((Zlength (lens1)) = count_pre)) (PreH34 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH35 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH36 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH37 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH38 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH39 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH40 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH41 : (PairedPermutation rows rows1 lens lens1)) (PreH42 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH43 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH44 : ((sum (lens1)) = (sum (lens)))) (PreH45 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat2)
  ** (intArray.full lengths_pre count_pre lens2)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
  ** ((( &( "pivot_length" ) )) # Int |->_)
|--
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens2) ”

noncomputable def quicksort_numbers_partial_solve_wit_23_pure_split_goal_8 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (rows2 : (List (List Int))) (lens2 : (List Int)) (flat2 : (List Int)) (PreH1 : (pivot <= INT_MAX)) (PreH2 : (high_pre <= INT_MAX)) (PreH3 : (low_pre <= INT_MAX)) (PreH4 : (number_width_pre <= INT_MAX)) (PreH5 : (count_pre <= INT_MAX)) (PreH6 : (pivot >= INT_MIN)) (PreH7 : (high_pre >= INT_MIN)) (PreH8 : (low_pre >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (count_pre >= INT_MIN)) (PreH11 : (pivot < high_pre)) (PreH12 : (FlatRows flat2 rows2 count_pre number_width_pre)) (PreH13 : (PairedPermutation rows1 rows2 lens1 lens2)) (PreH14 : (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1))) (PreH15 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1))) (PreH16 : (pivot > low_pre)) (PreH17 : ((0 : Int) <= (pivot * number_width_pre))) (PreH18 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH19 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH20 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH21 : (1 <= count_pre)) (PreH22 : (count_pre <= 20)) (PreH23 : (1 <= number_width_pre)) (PreH24 : (number_width_pre <= 10)) (PreH25 : ((0 : Int) <= low_pre)) (PreH26 : (low_pre < high_pre)) (PreH27 : (high_pre < count_pre)) (PreH28 : (low_pre <= pivot)) (PreH29 : (pivot <= high_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : ((Zlength (rows1)) = count_pre)) (PreH33 : ((Zlength (lens1)) = count_pre)) (PreH34 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH35 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH36 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH37 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH38 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH39 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH40 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH41 : (PairedPermutation rows rows1 lens lens1)) (PreH42 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH43 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH44 : ((sum (lens1)) = (sum (lens)))) (PreH45 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat2)
  ** (intArray.full lengths_pre count_pre lens2)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
  ** ((( &( "pivot_length" ) )) # Int |->_)
|--
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows2))) ”

noncomputable def quicksort_numbers_partial_solve_wit_23_pure_split_goal_9 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (rows2 : (List (List Int))) (lens2 : (List Int)) (flat2 : (List Int)) (PreH1 : (pivot <= INT_MAX)) (PreH2 : (high_pre <= INT_MAX)) (PreH3 : (low_pre <= INT_MAX)) (PreH4 : (number_width_pre <= INT_MAX)) (PreH5 : (count_pre <= INT_MAX)) (PreH6 : (pivot >= INT_MIN)) (PreH7 : (high_pre >= INT_MIN)) (PreH8 : (low_pre >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (count_pre >= INT_MIN)) (PreH11 : (pivot < high_pre)) (PreH12 : (FlatRows flat2 rows2 count_pre number_width_pre)) (PreH13 : (PairedPermutation rows1 rows2 lens1 lens2)) (PreH14 : (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1))) (PreH15 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1))) (PreH16 : (pivot > low_pre)) (PreH17 : ((0 : Int) <= (pivot * number_width_pre))) (PreH18 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH19 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH20 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH21 : (1 <= count_pre)) (PreH22 : (count_pre <= 20)) (PreH23 : (1 <= number_width_pre)) (PreH24 : (number_width_pre <= 10)) (PreH25 : ((0 : Int) <= low_pre)) (PreH26 : (low_pre < high_pre)) (PreH27 : (high_pre < count_pre)) (PreH28 : (low_pre <= pivot)) (PreH29 : (pivot <= high_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : ((Zlength (rows1)) = count_pre)) (PreH33 : ((Zlength (lens1)) = count_pre)) (PreH34 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH35 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH36 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH37 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH38 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH39 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH40 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH41 : (PairedPermutation rows rows1 lens lens1)) (PreH42 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH43 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH44 : ((sum (lens1)) = (sum (lens)))) (PreH45 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat2)
  ** (intArray.full lengths_pre count_pre lens2)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
  ** ((( &( "pivot_length" ) )) # Int |->_)
|--
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows2))) ”

noncomputable def quicksort_numbers_partial_solve_wit_23_pure_split_goal_10 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (rows2 : (List (List Int))) (lens2 : (List Int)) (flat2 : (List Int)) (PreH1 : (pivot <= INT_MAX)) (PreH2 : (high_pre <= INT_MAX)) (PreH3 : (low_pre <= INT_MAX)) (PreH4 : (number_width_pre <= INT_MAX)) (PreH5 : (count_pre <= INT_MAX)) (PreH6 : (pivot >= INT_MIN)) (PreH7 : (high_pre >= INT_MIN)) (PreH8 : (low_pre >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (count_pre >= INT_MIN)) (PreH11 : (pivot < high_pre)) (PreH12 : (FlatRows flat2 rows2 count_pre number_width_pre)) (PreH13 : (PairedPermutation rows1 rows2 lens1 lens2)) (PreH14 : (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1))) (PreH15 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1))) (PreH16 : (pivot > low_pre)) (PreH17 : ((0 : Int) <= (pivot * number_width_pre))) (PreH18 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH19 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH20 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH21 : (1 <= count_pre)) (PreH22 : (count_pre <= 20)) (PreH23 : (1 <= number_width_pre)) (PreH24 : (number_width_pre <= 10)) (PreH25 : ((0 : Int) <= low_pre)) (PreH26 : (low_pre < high_pre)) (PreH27 : (high_pre < count_pre)) (PreH28 : (low_pre <= pivot)) (PreH29 : (pivot <= high_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : ((Zlength (rows1)) = count_pre)) (PreH33 : ((Zlength (lens1)) = count_pre)) (PreH34 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH35 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH36 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH37 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH38 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH39 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH40 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH41 : (PairedPermutation rows rows1 lens lens1)) (PreH42 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH43 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH44 : ((sum (lens1)) = (sum (lens)))) (PreH45 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat2)
  ** (intArray.full lengths_pre count_pre lens2)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
  ** ((( &( "pivot_length" ) )) # Int |->_)
|--
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows2) (lens2))) ”

noncomputable def quicksort_numbers_partial_solve_wit_23_pure_split_goal_11 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (rows2 : (List (List Int))) (lens2 : (List Int)) (flat2 : (List Int)) (PreH1 : (pivot <= INT_MAX)) (PreH2 : (high_pre <= INT_MAX)) (PreH3 : (low_pre <= INT_MAX)) (PreH4 : (number_width_pre <= INT_MAX)) (PreH5 : (count_pre <= INT_MAX)) (PreH6 : (pivot >= INT_MIN)) (PreH7 : (high_pre >= INT_MIN)) (PreH8 : (low_pre >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (count_pre >= INT_MIN)) (PreH11 : (pivot < high_pre)) (PreH12 : (FlatRows flat2 rows2 count_pre number_width_pre)) (PreH13 : (PairedPermutation rows1 rows2 lens1 lens2)) (PreH14 : (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1))) (PreH15 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1))) (PreH16 : (pivot > low_pre)) (PreH17 : ((0 : Int) <= (pivot * number_width_pre))) (PreH18 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH19 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH20 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH21 : (1 <= count_pre)) (PreH22 : (count_pre <= 20)) (PreH23 : (1 <= number_width_pre)) (PreH24 : (number_width_pre <= 10)) (PreH25 : ((0 : Int) <= low_pre)) (PreH26 : (low_pre < high_pre)) (PreH27 : (high_pre < count_pre)) (PreH28 : (low_pre <= pivot)) (PreH29 : (pivot <= high_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : ((Zlength (rows1)) = count_pre)) (PreH33 : ((Zlength (lens1)) = count_pre)) (PreH34 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH35 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH36 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH37 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH38 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH39 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH40 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH41 : (PairedPermutation rows rows1 lens lens1)) (PreH42 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH43 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH44 : ((sum (lens1)) = (sum (lens)))) (PreH45 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat2)
  ** (intArray.full lengths_pre count_pre lens2)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
  ** ((( &( "pivot_length" ) )) # Int |->_)
|--
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows2) (lens2))) ”

noncomputable def quicksort_numbers_partial_solve_wit_23_aux : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (rows2 : (List (List Int))) (lens2 : (List Int)) (flat2 : (List Int)) (PreH1 : (pivot < high_pre)) (PreH2 : (FlatRows flat2 rows2 count_pre number_width_pre)) (PreH3 : (PairedPermutation rows1 rows2 lens1 lens2)) (PreH4 : (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1))) (PreH5 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1))) (PreH6 : (pivot > low_pre)) (PreH7 : ((0 : Int) <= (pivot * number_width_pre))) (PreH8 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH9 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH10 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH11 : (1 <= count_pre)) (PreH12 : (count_pre <= 20)) (PreH13 : (1 <= number_width_pre)) (PreH14 : (number_width_pre <= 10)) (PreH15 : ((0 : Int) <= low_pre)) (PreH16 : (low_pre < high_pre)) (PreH17 : (high_pre < count_pre)) (PreH18 : (low_pre <= pivot)) (PreH19 : (pivot <= high_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : ((Zlength (rows1)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH25 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH26 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH27 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH28 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH30 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH31 : (PairedPermutation rows rows1 lens lens1)) (PreH32 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH33 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH34 : ((sum (lens1)) = (sum (lens)))) (PreH35 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat2)
  ** (intArray.full lengths_pre count_pre lens2)
|--
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= (pivot + 1)) ” &&
  “ ((pivot + 1) <= count_pre) ” &&
  “ ((-1) <= high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (FlatRows flat2 rows2 count_pre number_width_pre) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows2) (lens2))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows2) (lens2))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows2))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows2))) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens2) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens2) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows2))) ” &&
  “ ((Zlength (lens2)) = count_pre) ” &&
  “ ((Zlength (rows2)) = count_pre) ” &&
  “ ((sum (lens2)) <= 200) ” &&
  “ (1 <= (sum (lens2))) ” &&
  “ (pivot < high_pre) ” &&
  “ (FlatRows flat2 rows2 count_pre number_width_pre) ” &&
  “ (PairedPermutation rows1 rows2 lens1 lens2) ” &&
  “ (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1)) ” &&
  “ (GreedySortedRange rows2 lens2 low_pre (pivot - 1)) ” &&
  “ (pivot > low_pre) ” &&
  “ ((0 : Int) <= (pivot * number_width_pre)) ” &&
  “ (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= pivot) ” &&
  “ (pivot <= high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ ((Zlength (rows1)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1))) ” &&
  “ (PairedPermutation rows rows1 lens lens1) ” &&
  “ (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre) ” &&
  “ (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat2)
  ** (intArray.full lengths_pre count_pre lens2)

noncomputable def quicksort_numbers_partial_solve_wit_23 : Prop := quicksort_numbers_partial_solve_wit_23_pure -> quicksort_numbers_partial_solve_wit_23_aux

noncomputable def quicksort_numbers_partial_solve_wit_24_pure : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (PreH1 : (pivot < high_pre)) (PreH2 : (pivot <= low_pre)) (PreH3 : ((0 : Int) <= (pivot * number_width_pre))) (PreH4 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH5 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH6 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH7 : (1 <= count_pre)) (PreH8 : (count_pre <= 20)) (PreH9 : (1 <= number_width_pre)) (PreH10 : (number_width_pre <= 10)) (PreH11 : ((0 : Int) <= low_pre)) (PreH12 : (low_pre < high_pre)) (PreH13 : (high_pre < count_pre)) (PreH14 : (low_pre <= pivot)) (PreH15 : (pivot <= high_pre)) (PreH16 : (1 <= (sum (lens)))) (PreH17 : ((sum (lens)) <= 200)) (PreH18 : ((Zlength (rows1)) = count_pre)) (PreH19 : ((Zlength (lens1)) = count_pre)) (PreH20 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH21 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH22 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH23 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH24 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH26 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH27 : (PairedPermutation rows rows1 lens lens1)) (PreH28 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH29 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "scan" ) )) # Int |->_)
  ** ((( &( "boundary" ) )) # Int |->_)
  ** ((( &( "pivot_length" ) )) # Int |->_)
|--
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= (pivot + 1)) ” &&
  “ ((pivot + 1) <= count_pre) ” &&
  “ ((-1) <= high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (1 <= (sum (lens1))) ” &&
  “ ((sum (lens1)) <= 200) ” &&
  “ ((Zlength (rows1)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”

noncomputable def quicksort_numbers_partial_solve_wit_24_aux : Prop :=
  forall (high_pre : Int) (low_pre : Int) (number_width_pre : Int) (count_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (pivot : Int) (rows1 : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (PreH1 : (pivot < high_pre)) (PreH2 : (pivot <= low_pre)) (PreH3 : ((0 : Int) <= (pivot * number_width_pre))) (PreH4 : (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH5 : ((0 : Int) <= (high_pre * number_width_pre))) (PreH6 : (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH7 : (1 <= count_pre)) (PreH8 : (count_pre <= 20)) (PreH9 : (1 <= number_width_pre)) (PreH10 : (number_width_pre <= 10)) (PreH11 : ((0 : Int) <= low_pre)) (PreH12 : (low_pre < high_pre)) (PreH13 : (high_pre < count_pre)) (PreH14 : (low_pre <= pivot)) (PreH15 : (pivot <= high_pre)) (PreH16 : (1 <= (sum (lens)))) (PreH17 : ((sum (lens)) <= 200)) (PreH18 : ((Zlength (rows1)) = count_pre)) (PreH19 : ((Zlength (lens1)) = count_pre)) (PreH20 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH21 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH22 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH23 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH24 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH26 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH27 : (PairedPermutation rows rows1 lens lens1)) (PreH28 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre)) (PreH29 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot)) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
|--
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= (pivot + 1)) ” &&
  “ ((pivot + 1) <= count_pre) ” &&
  “ ((-1) <= high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (1 <= (sum (lens1))) ” &&
  “ ((sum (lens1)) <= 200) ” &&
  “ ((Zlength (rows1)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ” &&
  “ (pivot < high_pre) ” &&
  “ (pivot <= low_pre) ” &&
  “ ((0 : Int) <= (pivot * number_width_pre)) ” &&
  “ (((pivot * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((0 : Int) <= (high_pre * number_width_pre)) ” &&
  “ (((high_pre * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre < high_pre) ” &&
  “ (high_pre < count_pre) ” &&
  “ (low_pre <= pivot) ” &&
  “ (pivot <= high_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ ((Zlength (rows1)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1))) ” &&
  “ (PairedPermutation rows rows1 lens lens1) ” &&
  “ (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre) ” &&
  “ (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)

noncomputable def quicksort_numbers_partial_solve_wit_24 : Prop := quicksort_numbers_partial_solve_wit_24_pure -> quicksort_numbers_partial_solve_wit_24_aux

noncomputable def concatenating_numbers_safety_wit_1 : Prop :=
  forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (1 <= (sum (lens)))) (PreH6 : ((sum (lens)) <= 200)) (PreH7 : ((Zlength (rows)) = count_pre)) (PreH8 : ((Zlength (lens)) = count_pre)) (PreH9 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows)))) (PreH10 : (Forall ((LE.le (α := Int)) (1)) lens)) (PreH11 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens)) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH13 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows) (lens)))) (PreH15 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows) (lens)))) (PreH16 : (FlatRows flat rows count_pre number_width_pre)) ,
  ((( &( "result_length" ) )) # Int |->_)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "result" ) )) # Ptr |-> (result_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat)
  ** (intArray.full lengths_pre count_pre lens)
  ** (intArray.undef_full result_pre (sum (lens)))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def concatenating_numbers_safety_wit_2 : Prop :=
  forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (1 <= (sum (lens)))) (PreH6 : ((sum (lens)) <= 200)) (PreH7 : ((Zlength (rows)) = count_pre)) (PreH8 : ((Zlength (lens)) = count_pre)) (PreH9 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows)))) (PreH10 : (Forall ((LE.le (α := Int)) (1)) lens)) (PreH11 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens)) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH13 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows) (lens)))) (PreH15 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows) (lens)))) (PreH16 : (FlatRows flat rows count_pre number_width_pre)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "result_length" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "result" ) )) # Ptr |-> (result_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat)
  ** (intArray.full lengths_pre count_pre lens)
  ** (intArray.undef_full result_pre (sum (lens)))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def concatenating_numbers_safety_wit_3 : Prop :=
  forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (count_pre > 1)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : ((Zlength (rows)) = count_pre)) (PreH9 : ((Zlength (lens)) = count_pre)) (PreH10 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) lens)) (PreH12 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens)) (PreH13 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH14 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows) (lens)))) (PreH16 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows) (lens)))) (PreH17 : (FlatRows flat rows count_pre number_width_pre)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "result_length" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "result" ) )) # Ptr |-> (result_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat)
  ** (intArray.full lengths_pre count_pre lens)
  ** (intArray.undef_full result_pre (sum (lens)))
|--
  “ ((count_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (count_pre - 1)) ”

noncomputable def concatenating_numbers_safety_wit_4 : Prop :=
  forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (count_pre > 1)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : ((Zlength (rows)) = count_pre)) (PreH9 : ((Zlength (lens)) = count_pre)) (PreH10 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) lens)) (PreH12 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens)) (PreH13 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH14 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows) (lens)))) (PreH16 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows) (lens)))) (PreH17 : (FlatRows flat rows count_pre number_width_pre)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "result_length" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "result" ) )) # Ptr |-> (result_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat)
  ** (intArray.full lengths_pre count_pre lens)
  ** (intArray.undef_full result_pre (sum (lens)))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def concatenating_numbers_safety_wit_5 : Prop :=
  forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (count_pre > 1)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : ((Zlength (rows)) = count_pre)) (PreH9 : ((Zlength (lens)) = count_pre)) (PreH10 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) lens)) (PreH12 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens)) (PreH13 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH14 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows) (lens)))) (PreH16 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows) (lens)))) (PreH17 : (FlatRows flat rows count_pre number_width_pre)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "result_length" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "result" ) )) # Ptr |-> (result_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat)
  ** (intArray.full lengths_pre count_pre lens)
  ** (intArray.undef_full result_pre (sum (lens)))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def concatenating_numbers_safety_wit_6 : Prop :=
  forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (lens1 : (List Int)) (flat1 : (List Int)) (rows1 : (List (List Int))) (PreH1 : (FlatRows flat1 rows1 count_pre number_width_pre)) (PreH2 : (PairedPermutation rows rows1 lens lens1)) (PreH3 : (SameOutsidePairedRange rows rows1 lens lens1 (0 : Int) (count_pre - 1))) (PreH4 : (GreedySortedRange rows1 lens1 (0 : Int) (count_pre - 1))) (PreH5 : (count_pre > 1)) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (1 <= (sum (lens)))) (PreH11 : ((sum (lens)) <= 200)) (PreH12 : ((Zlength (rows)) = count_pre)) (PreH13 : ((Zlength (lens)) = count_pre)) (PreH14 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows)))) (PreH15 : (Forall ((LE.le (α := Int)) (1)) lens)) (PreH16 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens)) (PreH17 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH18 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH19 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows) (lens)))) (PreH20 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows) (lens)))) (PreH21 : (FlatRows flat rows count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "result_length" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "result" ) )) # Ptr |-> (result_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** (intArray.undef_full result_pre (sum (lens)))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def concatenating_numbers_safety_wit_7 : Prop :=
  forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (count_pre <= 1)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : ((Zlength (rows)) = count_pre)) (PreH9 : ((Zlength (lens)) = count_pre)) (PreH10 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) lens)) (PreH12 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens)) (PreH13 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH14 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows) (lens)))) (PreH16 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows) (lens)))) (PreH17 : (FlatRows flat rows count_pre number_width_pre)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "result_length" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "result" ) )) # Ptr |-> (result_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat)
  ** (intArray.full lengths_pre count_pre lens)
  ** (intArray.undef_full result_pre (sum (lens)))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def concatenating_numbers_safety_wit_8 : Prop :=
  forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (result_length : Int) (output : (List Int)) (lens1 : (List Int)) (rows1 : (List (List Int))) (i : Int) (PreH1 : (i < count_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= count_pre)) (PreH10 : ((Zlength (rows1)) = count_pre)) (PreH11 : ((Zlength (lens1)) = count_pre)) (PreH12 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH13 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH14 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH15 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH16 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH17 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH18 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH19 : (PairedPermutation rows rows1 lens lens1)) (PreH20 : (GreedySorted rows1 lens1)) (PreH21 : ((sum (lens1)) = (sum (lens)))) (PreH22 : (output = (ConcatenatedPrefix (rows1) (lens1) (i)))) (PreH23 : (result_length = (Zlength (output)))) (PreH24 : ((0 : Int) <= result_length)) (PreH25 : (result_length <= (sum (lens)))) (PreH26 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "result" ) )) # Ptr |-> (result_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "result_length" ) )) # Int |-> (result_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** (intArray.seg result_pre (0 : Int) result_length output)
  ** (intArray.undef_seg result_pre result_length (sum (lens)))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def concatenating_numbers_safety_wit_9 : Prop :=
  forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (output : (List Int)) (rows1 : (List (List Int))) (result_length : Int) (lens1 : (List Int)) (j : Int) (i : Int) (PreH1 : (j < (Znth i lens1 (0 : Int)))) (PreH2 : ((0 : Int) <= (i * number_width_pre))) (PreH3 : (((i * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((j < (Znth (i) (lens1) ((0 : Int)))) -> (result_length < (sum (lens))))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < count_pre)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= (Znth (i) (lens1) ((0 : Int))))) (PreH15 : (1 <= (Znth (i) (lens1) ((0 : Int))))) (PreH16 : ((Znth (i) (lens1) ((0 : Int))) <= number_width_pre)) (PreH17 : ((Zlength (rows1)) = count_pre)) (PreH18 : ((Zlength (lens1)) = count_pre)) (PreH19 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH20 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH21 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH23 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH24 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH25 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH26 : (PairedPermutation rows rows1 lens lens1)) (PreH27 : (GreedySorted rows1 lens1)) (PreH28 : ((sum (lens1)) = (sum (lens)))) (PreH29 : (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j)))) (PreH30 : (result_length = (Zlength (output)))) (PreH31 : ((0 : Int) <= result_length)) (PreH32 : (result_length <= (sum (lens)))) (PreH33 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "result" ) )) # Ptr |-> (result_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "result_length" ) )) # Int |-> (result_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.seg result_pre (0 : Int) result_length output)
  ** (intArray.undef_seg result_pre result_length (sum (lens)))
|--
  “ (((i * number_width_pre) + j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((i * number_width_pre) + j)) ”

noncomputable def concatenating_numbers_safety_wit_10 : Prop :=
  forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (output : (List Int)) (rows1 : (List (List Int))) (result_length : Int) (lens1 : (List Int)) (j : Int) (i : Int) (PreH1 : (j < (Znth i lens1 (0 : Int)))) (PreH2 : ((0 : Int) <= (i * number_width_pre))) (PreH3 : (((i * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((j < (Znth (i) (lens1) ((0 : Int)))) -> (result_length < (sum (lens))))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < count_pre)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= (Znth (i) (lens1) ((0 : Int))))) (PreH15 : (1 <= (Znth (i) (lens1) ((0 : Int))))) (PreH16 : ((Znth (i) (lens1) ((0 : Int))) <= number_width_pre)) (PreH17 : ((Zlength (rows1)) = count_pre)) (PreH18 : ((Zlength (lens1)) = count_pre)) (PreH19 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH20 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH21 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH23 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH24 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH25 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH26 : (PairedPermutation rows rows1 lens lens1)) (PreH27 : (GreedySorted rows1 lens1)) (PreH28 : ((sum (lens1)) = (sum (lens)))) (PreH29 : (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j)))) (PreH30 : (result_length = (Zlength (output)))) (PreH31 : ((0 : Int) <= result_length)) (PreH32 : (result_length <= (sum (lens)))) (PreH33 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "result" ) )) # Ptr |-> (result_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "result_length" ) )) # Int |-> (result_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.seg result_pre (0 : Int) result_length output)
  ** (intArray.undef_seg result_pre result_length (sum (lens)))
|--
  “ ((i * number_width_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i * number_width_pre)) ”

noncomputable def concatenating_numbers_safety_wit_11 : Prop :=
  forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (output : (List Int)) (rows1 : (List (List Int))) (result_length : Int) (lens1 : (List Int)) (j : Int) (i : Int) (PreH1 : (j < (Znth i lens1 (0 : Int)))) (PreH2 : ((0 : Int) <= (i * number_width_pre))) (PreH3 : (((i * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((j < (Znth (i) (lens1) ((0 : Int)))) -> (result_length < (sum (lens))))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < count_pre)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= (Znth (i) (lens1) ((0 : Int))))) (PreH15 : (1 <= (Znth (i) (lens1) ((0 : Int))))) (PreH16 : ((Znth (i) (lens1) ((0 : Int))) <= number_width_pre)) (PreH17 : ((Zlength (rows1)) = count_pre)) (PreH18 : ((Zlength (lens1)) = count_pre)) (PreH19 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH20 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH21 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH23 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH24 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH25 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH26 : (PairedPermutation rows rows1 lens lens1)) (PreH27 : (GreedySorted rows1 lens1)) (PreH28 : ((sum (lens1)) = (sum (lens)))) (PreH29 : (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j)))) (PreH30 : (result_length = (Zlength (output)))) (PreH31 : ((0 : Int) <= result_length)) (PreH32 : (result_length <= (sum (lens)))) (PreH33 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.seg result_pre (0 : Int) (result_length + 1) (output ++ ((Znth ((i * number_width_pre) + j) flat1 (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg result_pre (result_length + 1) (sum (lens)))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "result" ) )) # Ptr |-> (result_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "result_length" ) )) # Int |-> (result_length))
|--
  “ ((result_length + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (result_length + 1)) ”

noncomputable def concatenating_numbers_safety_wit_12 : Prop :=
  forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (output : (List Int)) (rows1 : (List (List Int))) (result_length : Int) (lens1 : (List Int)) (j : Int) (i : Int) (PreH1 : (j < (Znth i lens1 (0 : Int)))) (PreH2 : ((0 : Int) <= (i * number_width_pre))) (PreH3 : (((i * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((j < (Znth (i) (lens1) ((0 : Int)))) -> (result_length < (sum (lens))))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < count_pre)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= (Znth (i) (lens1) ((0 : Int))))) (PreH15 : (1 <= (Znth (i) (lens1) ((0 : Int))))) (PreH16 : ((Znth (i) (lens1) ((0 : Int))) <= number_width_pre)) (PreH17 : ((Zlength (rows1)) = count_pre)) (PreH18 : ((Zlength (lens1)) = count_pre)) (PreH19 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH20 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH21 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH23 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH24 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH25 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH26 : (PairedPermutation rows rows1 lens lens1)) (PreH27 : (GreedySorted rows1 lens1)) (PreH28 : ((sum (lens1)) = (sum (lens)))) (PreH29 : (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j)))) (PreH30 : (result_length = (Zlength (output)))) (PreH31 : ((0 : Int) <= result_length)) (PreH32 : (result_length <= (sum (lens)))) (PreH33 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.seg result_pre (0 : Int) (result_length + 1) (output ++ ((Znth ((i * number_width_pre) + j) flat1 (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg result_pre (result_length + 1) (sum (lens)))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "result" ) )) # Ptr |-> (result_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "result_length" ) )) # Int |-> ((result_length + 1)))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def concatenating_numbers_safety_wit_13 : Prop :=
  forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (output : (List Int)) (rows1 : (List (List Int))) (result_length : Int) (lens1 : (List Int)) (j : Int) (i : Int) (PreH1 : (j >= (Znth i lens1 (0 : Int)))) (PreH2 : ((0 : Int) <= (i * number_width_pre))) (PreH3 : (((i * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((j < (Znth (i) (lens1) ((0 : Int)))) -> (result_length < (sum (lens))))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < count_pre)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= (Znth (i) (lens1) ((0 : Int))))) (PreH15 : (1 <= (Znth (i) (lens1) ((0 : Int))))) (PreH16 : ((Znth (i) (lens1) ((0 : Int))) <= number_width_pre)) (PreH17 : ((Zlength (rows1)) = count_pre)) (PreH18 : ((Zlength (lens1)) = count_pre)) (PreH19 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH20 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH21 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH23 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH24 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH25 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH26 : (PairedPermutation rows rows1 lens lens1)) (PreH27 : (GreedySorted rows1 lens1)) (PreH28 : ((sum (lens1)) = (sum (lens)))) (PreH29 : (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j)))) (PreH30 : (result_length = (Zlength (output)))) (PreH31 : ((0 : Int) <= result_length)) (PreH32 : (result_length <= (sum (lens)))) (PreH33 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full lengths_pre count_pre lens1)
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "result" ) )) # Ptr |-> (result_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "result_length" ) )) # Int |-> (result_length))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.seg result_pre (0 : Int) result_length output)
  ** (intArray.undef_seg result_pre result_length (sum (lens)))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def concatenating_numbers_entail_wit_1 : Prop :=
  (
forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (1 <= (sum (lens)))) (PreH6 : ((sum (lens)) <= 200)) (PreH7 : ((Zlength (rows)) = count_pre)) (PreH8 : ((Zlength (lens)) = count_pre)) (PreH9 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows)))) (PreH10 : (Forall ((LE.le (α := Int)) (1)) lens)) (PreH11 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens)) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH13 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows) (lens)))) (PreH15 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows) (lens)))) (PreH16 : (flat = (List.flatten (rows)))) (PreH17 : (Forall ((GE.ge (α := Int)) (1000000000)) (DecimalRowValues (rows) (lens)))) ,
  (intArray2.full numbers_pre count_pre number_width_pre rows)
  ** (intArray.full lengths_pre count_pre lens)
  ** (intArray.undef_full result_pre (sum (lens)))
|--
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ ((Zlength (rows)) = count_pre) ” &&
  “ ((Zlength (lens)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows) (lens))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows) (lens))) ” &&
  “ (FlatRows flat rows count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat)
  ** (intArray.full lengths_pre count_pre lens)
  ** (intArray.undef_full result_pre (sum (lens)))
) \/
(
forall (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (1 <= (sum (lens)))) (PreH6 : ((sum (lens)) <= 200)) (PreH7 : ((Zlength (rows)) = count_pre)) (PreH8 : ((Zlength (lens)) = count_pre)) (PreH9 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows)))) (PreH10 : (Forall ((LE.le (α := Int)) (1)) lens)) (PreH11 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens)) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH13 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows) (lens)))) (PreH15 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows) (lens)))) (PreH16 : (flat = (List.flatten (rows)))) (PreH17 : (Forall ((GE.ge (α := Int)) (1000000000)) (DecimalRowValues (rows) (lens)))) ,
  (intArray2.full numbers_pre count_pre number_width_pre rows)
|--
  “ (FlatRows flat rows count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat)
)

noncomputable def concatenating_numbers_entail_wit_1_split_goal_1 : Prop :=
  forall (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (1 <= (sum (lens)))) (PreH6 : ((sum (lens)) <= 200)) (PreH7 : ((Zlength (rows)) = count_pre)) (PreH8 : ((Zlength (lens)) = count_pre)) (PreH9 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows)))) (PreH10 : (Forall ((LE.le (α := Int)) (1)) lens)) (PreH11 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens)) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH13 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows) (lens)))) (PreH15 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows) (lens)))) (PreH16 : (flat = (List.flatten (rows)))) (PreH17 : (Forall ((GE.ge (α := Int)) (1000000000)) (DecimalRowValues (rows) (lens)))) ,
  (intArray2.full numbers_pre count_pre number_width_pre rows)
|--
  “ (FlatRows flat rows count_pre number_width_pre) ”

noncomputable def concatenating_numbers_entail_wit_1_split_goal_spatial : Prop :=
  forall (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (1 <= (sum (lens)))) (PreH6 : ((sum (lens)) <= 200)) (PreH7 : ((Zlength (rows)) = count_pre)) (PreH8 : ((Zlength (lens)) = count_pre)) (PreH9 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows)))) (PreH10 : (Forall ((LE.le (α := Int)) (1)) lens)) (PreH11 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens)) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH13 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows) (lens)))) (PreH15 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows) (lens)))) (PreH16 : (flat = (List.flatten (rows)))) (PreH17 : (Forall ((GE.ge (α := Int)) (1000000000)) (DecimalRowValues (rows) (lens)))) ,
  (intArray2.full numbers_pre count_pre number_width_pre rows)
|--
  (intArray.full numbers_pre (count_pre * number_width_pre) flat)

noncomputable def concatenating_numbers_entail_wit_2_1 : Prop :=
  (
forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (lens1_2 : (List Int)) (flat1_2 : (List Int)) (rows1_2 : (List (List Int))) (PreH1 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) (PreH2 : (PairedPermutation rows rows1_2 lens lens1_2)) (PreH3 : (SameOutsidePairedRange rows rows1_2 lens lens1_2 (0 : Int) (count_pre - 1))) (PreH4 : (GreedySortedRange rows1_2 lens1_2 (0 : Int) (count_pre - 1))) (PreH5 : (count_pre > 1)) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (1 <= (sum (lens)))) (PreH11 : ((sum (lens)) <= 200)) (PreH12 : ((Zlength (rows)) = count_pre)) (PreH13 : ((Zlength (lens)) = count_pre)) (PreH14 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows)))) (PreH15 : (Forall ((LE.le (α := Int)) (1)) lens)) (PreH16 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens)) (PreH17 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH18 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH19 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows) (lens)))) (PreH20 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows) (lens)))) (PreH21 : (FlatRows flat rows count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1_2)
  ** (intArray.full lengths_pre count_pre lens1_2)
  ** (intArray.undef_full result_pre (sum (lens)))
|--
  EX flat1 : (List Int), EX output : (List Int), EX lens1 : (List Int), EX rows1 : (List (List Int)),
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= count_pre) ” &&
  “ ((Zlength (rows1)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1))) ” &&
  “ (PairedPermutation rows rows1 lens lens1) ” &&
  “ (GreedySorted rows1 lens1) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (output = (ConcatenatedPrefix (rows1) (lens1) ((0 : Int)))) ” &&
  “ ((0 : Int) = (Zlength (output))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** (intArray.seg result_pre (0 : Int) (0 : Int) output)
  ** (intArray.undef_seg result_pre (0 : Int) (sum (lens)))
) \/
(
forall (number_width_pre : Int) (count_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (lens1_2 : (List Int)) (flat1_2 : (List Int)) (rows1_2 : (List (List Int))) (PreH1 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) (PreH2 : (PairedPermutation rows rows1_2 lens lens1_2)) (PreH3 : (SameOutsidePairedRange rows rows1_2 lens lens1_2 (0 : Int) (count_pre - 1))) (PreH4 : (GreedySortedRange rows1_2 lens1_2 (0 : Int) (count_pre - 1))) (PreH5 : (count_pre > 1)) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (1 <= (sum (lens)))) (PreH11 : ((sum (lens)) <= 200)) (PreH12 : ((Zlength (rows)) = count_pre)) (PreH13 : ((Zlength (lens)) = count_pre)) (PreH14 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows)))) (PreH15 : (Forall ((LE.le (α := Int)) (1)) lens)) (PreH16 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens)) (PreH17 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH18 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH19 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows) (lens)))) (PreH20 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows) (lens)))) (PreH21 : (FlatRows flat rows count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (Zlength (rows))) ” &&
  “ ((Zlength (rows1)) = (Zlength (rows))) ” &&
  “ ((Zlength (lens1_2)) = (Zlength (rows))) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1_2) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1_2))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1_2))) ” &&
  “ (PairedPermutation rows rows1 lens lens1_2) ” &&
  “ (GreedySorted rows1 lens1_2) ” &&
  “ ((sum (lens1_2)) = (sum (lens))) ” &&
  “ ((@List.nil Int) = (ConcatenatedPrefix (rows1) (lens1_2) ((0 : Int)))) ” &&
  “ ((0 : Int) = (Zlength ((@List.nil Int)))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (sum (lens))) ” &&
  “ (FlatRows flat1_2 rows1 (Zlength (rows)) number_width_pre) ”
  &&  emp
)

noncomputable def concatenating_numbers_entail_wit_2_2 : Prop :=
  (
forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (count_pre <= 1)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : ((Zlength (rows)) = count_pre)) (PreH9 : ((Zlength (lens)) = count_pre)) (PreH10 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) lens)) (PreH12 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens)) (PreH13 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH14 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows) (lens)))) (PreH16 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows) (lens)))) (PreH17 : (FlatRows flat rows count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat)
  ** (intArray.full lengths_pre count_pre lens)
  ** (intArray.undef_full result_pre (sum (lens)))
|--
  EX flat1 : (List Int), EX output : (List Int), EX lens1 : (List Int), EX rows1 : (List (List Int)),
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= count_pre) ” &&
  “ ((Zlength (rows1)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1))) ” &&
  “ (PairedPermutation rows rows1 lens lens1) ” &&
  “ (GreedySorted rows1 lens1) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (output = (ConcatenatedPrefix (rows1) (lens1) ((0 : Int)))) ” &&
  “ ((0 : Int) = (Zlength (output))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** (intArray.seg result_pre (0 : Int) (0 : Int) output)
  ** (intArray.undef_seg result_pre (0 : Int) (sum (lens)))
) \/
(
forall (number_width_pre : Int) (count_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (count_pre <= 1)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : ((Zlength (rows)) = count_pre)) (PreH9 : ((Zlength (lens)) = count_pre)) (PreH10 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) lens)) (PreH12 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens)) (PreH13 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH14 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows) (lens)))) (PreH16 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows) (lens)))) (PreH17 : (FlatRows flat rows count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (Zlength (rows))) ” &&
  “ ((Zlength (rows1)) = (Zlength (rows))) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens))) ” &&
  “ (PairedPermutation rows rows1 lens lens) ” &&
  “ (GreedySorted rows1 lens) ” &&
  “ ((@List.nil Int) = (ConcatenatedPrefix (rows1) (lens) ((0 : Int)))) ” &&
  “ ((0 : Int) = (Zlength ((@List.nil Int)))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (sum (lens))) ” &&
  “ (FlatRows flat rows1 (Zlength (rows)) number_width_pre) ”
  &&  emp
)

noncomputable def concatenating_numbers_entail_wit_3 : Prop :=
  (
forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1_2 : (List Int)) (result_length : Int) (output_2 : (List Int)) (lens1_2 : (List Int)) (rows1_2 : (List (List Int))) (i : Int) (PreH1 : (i < count_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= count_pre)) (PreH10 : ((Zlength (rows1_2)) = count_pre)) (PreH11 : ((Zlength (lens1_2)) = count_pre)) (PreH12 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1_2)))) (PreH13 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH15 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH16 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH17 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1_2) (lens1_2)))) (PreH18 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1_2) (lens1_2)))) (PreH19 : (PairedPermutation rows rows1_2 lens lens1_2)) (PreH20 : (GreedySorted rows1_2 lens1_2)) (PreH21 : ((sum (lens1_2)) = (sum (lens)))) (PreH22 : (output_2 = (ConcatenatedPrefix (rows1_2) (lens1_2) (i)))) (PreH23 : (result_length = (Zlength (output_2)))) (PreH24 : ((0 : Int) <= result_length)) (PreH25 : (result_length <= (sum (lens)))) (PreH26 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1_2)
  ** (intArray.full lengths_pre count_pre lens1_2)
  ** (intArray.seg result_pre (0 : Int) result_length output_2)
  ** (intArray.undef_seg result_pre result_length (sum (lens)))
|--
  EX flat1 : (List Int), EX output : (List Int), EX rows1 : (List (List Int)), EX lens1 : (List Int),
  “ ((0 : Int) <= (i * number_width_pre)) ” &&
  “ (((i * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (((0 : Int) < (Znth (i) (lens1) ((0 : Int)))) -> (result_length < (sum (lens)))) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < count_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (Znth (i) (lens1) ((0 : Int)))) ” &&
  “ (1 <= (Znth (i) (lens1) ((0 : Int)))) ” &&
  “ ((Znth (i) (lens1) ((0 : Int))) <= number_width_pre) ” &&
  “ ((Zlength (rows1)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1))) ” &&
  “ (PairedPermutation rows rows1 lens lens1) ” &&
  “ (GreedySorted rows1 lens1) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) ((0 : Int)))) ” &&
  “ (result_length = (Zlength (output))) ” &&
  “ ((0 : Int) <= result_length) ” &&
  “ (result_length <= (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** (intArray.seg result_pre (0 : Int) result_length output)
  ** (intArray.undef_seg result_pre result_length (sum (lens)))
) \/
(
forall (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1_2 : (List Int)) (result_length : Int) (output_2 : (List Int)) (lens1_2 : (List Int)) (rows1_2 : (List (List Int))) (i : Int) (PreH1 : (i < count_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= count_pre)) (PreH10 : ((Zlength (rows1_2)) = count_pre)) (PreH11 : ((Zlength (lens1_2)) = count_pre)) (PreH12 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1_2)))) (PreH13 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH15 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH16 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH17 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1_2) (lens1_2)))) (PreH18 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1_2) (lens1_2)))) (PreH19 : (PairedPermutation rows rows1_2 lens lens1_2)) (PreH20 : (GreedySorted rows1_2 lens1_2)) (PreH21 : ((sum (lens1_2)) = (sum (lens)))) (PreH22 : (output_2 = (ConcatenatedPrefix (rows1_2) (lens1_2) (i)))) (PreH23 : (result_length = (Zlength (output_2)))) (PreH24 : ((0 : Int) <= result_length)) (PreH25 : (result_length <= (sum (lens)))) (PreH26 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ ((ConcatenatedPrefix (rows1_2) (lens1_2) (i)) = (ConcatenatedOutputPrefix (rows1) (lens1_2) (i) ((0 : Int)))) ” &&
  “ ((0 : Int) <= (i * number_width_pre)) ” &&
  “ (((i * number_width_pre) + number_width_pre) <= ((Zlength (rows1_2)) * number_width_pre)) ” &&
  “ (((0 : Int) < (Znth (i) (lens1_2) ((0 : Int)))) -> ((Zlength (output_2)) < (sum (lens)))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (Znth (i) (lens1_2) ((0 : Int)))) ” &&
  “ (1 <= (Znth (i) (lens1_2) ((0 : Int)))) ” &&
  “ ((Znth (i) (lens1_2) ((0 : Int))) <= number_width_pre) ” &&
  “ ((Zlength (rows1)) = (Zlength (rows1_2))) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1_2))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1_2))) ” &&
  “ (PairedPermutation rows rows1 lens lens1_2) ” &&
  “ (GreedySorted rows1 lens1_2) ” &&
  “ ((Zlength (output_2)) = (Zlength ((ConcatenatedOutputPrefix (rows1) (lens1_2) (i) ((0 : Int)))))) ” &&
  “ (FlatRows flat1_2 rows1 (Zlength (rows1_2)) number_width_pre) ”
  &&  emp
)

noncomputable def concatenating_numbers_entail_wit_4 : Prop :=
  (
forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1_2 : (List Int)) (output_2 : (List Int)) (rows1_2 : (List (List Int))) (result_length : Int) (lens1_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j < (Znth i lens1_2 (0 : Int)))) (PreH2 : ((0 : Int) <= (i * number_width_pre))) (PreH3 : (((i * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((j < (Znth (i) (lens1_2) ((0 : Int)))) -> (result_length < (sum (lens))))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < count_pre)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= (Znth (i) (lens1_2) ((0 : Int))))) (PreH15 : (1 <= (Znth (i) (lens1_2) ((0 : Int))))) (PreH16 : ((Znth (i) (lens1_2) ((0 : Int))) <= number_width_pre)) (PreH17 : ((Zlength (rows1_2)) = count_pre)) (PreH18 : ((Zlength (lens1_2)) = count_pre)) (PreH19 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1_2)))) (PreH20 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH21 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH23 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH24 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1_2) (lens1_2)))) (PreH25 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1_2) (lens1_2)))) (PreH26 : (PairedPermutation rows rows1_2 lens lens1_2)) (PreH27 : (GreedySorted rows1_2 lens1_2)) (PreH28 : ((sum (lens1_2)) = (sum (lens)))) (PreH29 : (output_2 = (ConcatenatedOutputPrefix (rows1_2) (lens1_2) (i) (j)))) (PreH30 : (result_length = (Zlength (output_2)))) (PreH31 : ((0 : Int) <= result_length)) (PreH32 : (result_length <= (sum (lens)))) (PreH33 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  (intArray.seg result_pre (0 : Int) (result_length + 1) (output_2 ++ ((Znth ((i * number_width_pre) + j) flat1_2 (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg result_pre (result_length + 1) (sum (lens)))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1_2)
  ** (intArray.full lengths_pre count_pre lens1_2)
|--
  EX flat1 : (List Int), EX output : (List Int), EX rows1 : (List (List Int)), EX lens1 : (List Int),
  “ ((0 : Int) <= (i * number_width_pre)) ” &&
  “ (((i * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ (((j + 1) < (Znth (i) (lens1) ((0 : Int)))) -> ((result_length + 1) < (sum (lens)))) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < count_pre) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (Znth (i) (lens1) ((0 : Int)))) ” &&
  “ (1 <= (Znth (i) (lens1) ((0 : Int)))) ” &&
  “ ((Znth (i) (lens1) ((0 : Int))) <= number_width_pre) ” &&
  “ ((Zlength (rows1)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1))) ” &&
  “ (PairedPermutation rows rows1 lens lens1) ” &&
  “ (GreedySorted rows1 lens1) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) ((j + 1)))) ” &&
  “ ((result_length + 1) = (Zlength (output))) ” &&
  “ ((0 : Int) <= (result_length + 1)) ” &&
  “ ((result_length + 1) <= (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** (intArray.seg result_pre (0 : Int) (result_length + 1) output)
  ** (intArray.undef_seg result_pre (result_length + 1) (sum (lens)))
) \/
(
forall (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1_2 : (List Int)) (output_2 : (List Int)) (rows1_2 : (List (List Int))) (result_length : Int) (lens1_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j < (Znth i lens1_2 (0 : Int)))) (PreH2 : ((0 : Int) <= (i * number_width_pre))) (PreH3 : (((i * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((j < (Znth (i) (lens1_2) ((0 : Int)))) -> (result_length < (sum (lens))))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < count_pre)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= (Znth (i) (lens1_2) ((0 : Int))))) (PreH15 : (1 <= (Znth (i) (lens1_2) ((0 : Int))))) (PreH16 : ((Znth (i) (lens1_2) ((0 : Int))) <= number_width_pre)) (PreH17 : ((Zlength (rows1_2)) = count_pre)) (PreH18 : ((Zlength (lens1_2)) = count_pre)) (PreH19 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1_2)))) (PreH20 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH21 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH23 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH24 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1_2) (lens1_2)))) (PreH25 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1_2) (lens1_2)))) (PreH26 : (PairedPermutation rows rows1_2 lens lens1_2)) (PreH27 : (GreedySorted rows1_2 lens1_2)) (PreH28 : ((sum (lens1_2)) = (sum (lens)))) (PreH29 : (output_2 = (ConcatenatedOutputPrefix (rows1_2) (lens1_2) (i) (j)))) (PreH30 : (result_length = (Zlength (output_2)))) (PreH31 : ((0 : Int) <= result_length)) (PreH32 : (result_length <= (sum (lens)))) (PreH33 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ (((ConcatenatedOutputPrefix (rows1_2) (lens1_2) (i) (j)) ++ ((Znth ((i * number_width_pre) + j) flat1_2 (0 : Int)) :: (@List.nil Int))) = (ConcatenatedOutputPrefix (rows1) (lens1_2) (i) ((j + 1)))) ” &&
  “ (((j + 1) < (Znth (i) (lens1_2) ((0 : Int)))) -> (((Zlength (output_2)) + 1) < (sum (lens)))) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (Znth (i) (lens1_2) ((0 : Int)))) ” &&
  “ ((Zlength (rows1)) = (Zlength (rows1_2))) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1_2))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1_2))) ” &&
  “ (PairedPermutation rows rows1 lens lens1_2) ” &&
  “ (GreedySorted rows1 lens1_2) ” &&
  “ (((Zlength (output_2)) + 1) = (Zlength ((ConcatenatedOutputPrefix (rows1) (lens1_2) (i) ((j + 1)))))) ” &&
  “ ((0 : Int) <= ((Zlength (output_2)) + 1)) ” &&
  “ (((Zlength (output_2)) + 1) <= (sum (lens))) ” &&
  “ (FlatRows flat1_2 rows1 (Zlength (rows1_2)) number_width_pre) ”
  &&  emp
)

noncomputable def concatenating_numbers_entail_wit_5 : Prop :=
  (
forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1_2 : (List Int)) (output_2 : (List Int)) (rows1_2 : (List (List Int))) (result_length : Int) (lens1_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j >= (Znth i lens1_2 (0 : Int)))) (PreH2 : ((0 : Int) <= (i * number_width_pre))) (PreH3 : (((i * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((j < (Znth (i) (lens1_2) ((0 : Int)))) -> (result_length < (sum (lens))))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < count_pre)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= (Znth (i) (lens1_2) ((0 : Int))))) (PreH15 : (1 <= (Znth (i) (lens1_2) ((0 : Int))))) (PreH16 : ((Znth (i) (lens1_2) ((0 : Int))) <= number_width_pre)) (PreH17 : ((Zlength (rows1_2)) = count_pre)) (PreH18 : ((Zlength (lens1_2)) = count_pre)) (PreH19 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1_2)))) (PreH20 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH21 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH23 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH24 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1_2) (lens1_2)))) (PreH25 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1_2) (lens1_2)))) (PreH26 : (PairedPermutation rows rows1_2 lens lens1_2)) (PreH27 : (GreedySorted rows1_2 lens1_2)) (PreH28 : ((sum (lens1_2)) = (sum (lens)))) (PreH29 : (output_2 = (ConcatenatedOutputPrefix (rows1_2) (lens1_2) (i) (j)))) (PreH30 : (result_length = (Zlength (output_2)))) (PreH31 : ((0 : Int) <= result_length)) (PreH32 : (result_length <= (sum (lens)))) (PreH33 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  (intArray.full lengths_pre count_pre lens1_2)
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1_2)
  ** (intArray.seg result_pre (0 : Int) result_length output_2)
  ** (intArray.undef_seg result_pre result_length (sum (lens)))
|--
  EX flat1 : (List Int), EX output : (List Int), EX lens1 : (List Int), EX rows1 : (List (List Int)),
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= count_pre) ” &&
  “ ((Zlength (rows1)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1))) ” &&
  “ (PairedPermutation rows rows1 lens lens1) ” &&
  “ (GreedySorted rows1 lens1) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (output = (ConcatenatedPrefix (rows1) (lens1) ((i + 1)))) ” &&
  “ (result_length = (Zlength (output))) ” &&
  “ ((0 : Int) <= result_length) ” &&
  “ (result_length <= (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** (intArray.seg result_pre (0 : Int) result_length output)
  ** (intArray.undef_seg result_pre result_length (sum (lens)))
) \/
(
forall (number_width_pre : Int) (count_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1_2 : (List Int)) (output_2 : (List Int)) (rows1_2 : (List (List Int))) (result_length : Int) (lens1_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j >= (Znth i lens1_2 (0 : Int)))) (PreH2 : ((0 : Int) <= (i * number_width_pre))) (PreH3 : (((i * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((j < (Znth (i) (lens1_2) ((0 : Int)))) -> (result_length < (sum (lens))))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < count_pre)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= (Znth (i) (lens1_2) ((0 : Int))))) (PreH15 : (1 <= (Znth (i) (lens1_2) ((0 : Int))))) (PreH16 : ((Znth (i) (lens1_2) ((0 : Int))) <= number_width_pre)) (PreH17 : ((Zlength (rows1_2)) = count_pre)) (PreH18 : ((Zlength (lens1_2)) = count_pre)) (PreH19 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1_2)))) (PreH20 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH21 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH23 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH24 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1_2) (lens1_2)))) (PreH25 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1_2) (lens1_2)))) (PreH26 : (PairedPermutation rows rows1_2 lens lens1_2)) (PreH27 : (GreedySorted rows1_2 lens1_2)) (PreH28 : ((sum (lens1_2)) = (sum (lens)))) (PreH29 : (output_2 = (ConcatenatedOutputPrefix (rows1_2) (lens1_2) (i) (j)))) (PreH30 : (result_length = (Zlength (output_2)))) (PreH31 : ((0 : Int) <= result_length)) (PreH32 : (result_length <= (sum (lens)))) (PreH33 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre)) ,
  TT && emp 
|--
  EX rows1 : (List (List Int)),
  “ ((ConcatenatedOutputPrefix (rows1_2) (lens1_2) (i) (j)) = (ConcatenatedPrefix (rows1) (lens1_2) ((i + 1)))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (Zlength (rows1_2))) ” &&
  “ ((Zlength (rows1)) = (Zlength (rows1_2))) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1_2))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1_2))) ” &&
  “ (PairedPermutation rows rows1 lens lens1_2) ” &&
  “ (GreedySorted rows1 lens1_2) ” &&
  “ ((Zlength (output_2)) = (Zlength ((ConcatenatedPrefix (rows1) (lens1_2) ((i + 1)))))) ” &&
  “ (FlatRows flat1_2 rows1 (Zlength (rows1_2)) number_width_pre) ”
  &&  emp
)

noncomputable def concatenating_numbers_return_wit_1 : Prop :=
  (
forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (result_length : Int) (output_2 : (List Int)) (lens1_2 : (List Int)) (rows1_2 : (List (List Int))) (i : Int) (PreH1 : (i >= count_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= count_pre)) (PreH10 : ((Zlength (rows1_2)) = count_pre)) (PreH11 : ((Zlength (lens1_2)) = count_pre)) (PreH12 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1_2)))) (PreH13 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH15 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH16 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH17 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1_2) (lens1_2)))) (PreH18 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1_2) (lens1_2)))) (PreH19 : (PairedPermutation rows rows1_2 lens lens1_2)) (PreH20 : (GreedySorted rows1_2 lens1_2)) (PreH21 : ((sum (lens1_2)) = (sum (lens)))) (PreH22 : (output_2 = (ConcatenatedPrefix (rows1_2) (lens1_2) (i)))) (PreH23 : (result_length = (Zlength (output_2)))) (PreH24 : ((0 : Int) <= result_length)) (PreH25 : (result_length <= (sum (lens)))) (PreH26 : (FlatRows flat1 rows1_2 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1_2)
  ** (intArray.seg result_pre (0 : Int) result_length output_2)
  ** (intArray.undef_seg result_pre result_length (sum (lens)))
|--
  EX lens1 : (List Int), EX rows1 : (List (List Int)), EX output : (List Int),
  “ (result_pre = result_pre) ” &&
  “ (LargestConcatenation rows lens output) ”
  &&  (intArray2.full numbers_pre count_pre number_width_pre rows1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** (intArray.full result_pre (sum (lens)) output)
) \/
(
forall (result_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (result_length : Int) (output_2 : (List Int)) (lens1_2 : (List Int)) (rows1_2 : (List (List Int))) (i : Int) (PreH1 : (i >= count_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= count_pre)) (PreH10 : ((Zlength (rows1_2)) = count_pre)) (PreH11 : ((Zlength (lens1_2)) = count_pre)) (PreH12 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1_2)))) (PreH13 : (Forall ((LE.le (α := Int)) (1)) lens1_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1_2)) (PreH15 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH16 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1_2)))) (PreH17 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1_2) (lens1_2)))) (PreH18 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1_2) (lens1_2)))) (PreH19 : (PairedPermutation rows rows1_2 lens lens1_2)) (PreH20 : (GreedySorted rows1_2 lens1_2)) (PreH21 : ((sum (lens1_2)) = (sum (lens)))) (PreH22 : (output_2 = (ConcatenatedPrefix (rows1_2) (lens1_2) (i)))) (PreH23 : (result_length = (Zlength (output_2)))) (PreH24 : ((0 : Int) <= result_length)) (PreH25 : (result_length <= (sum (lens)))) (PreH26 : (FlatRows flat1 rows1_2 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.seg result_pre (0 : Int) result_length output_2)
  ** (intArray.undef_seg result_pre result_length (sum (lens)))
|--
  EX rows1 : (List (List Int)), EX output : (List Int),
  “ (LargestConcatenation rows lens output) ”
  &&  (intArray2.full numbers_pre count_pre number_width_pre rows1)
  ** (intArray.full result_pre (sum (lens)) output)
)

noncomputable def concatenating_numbers_partial_solve_wit_1_pure : Prop :=
  forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (count_pre > 1)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : ((Zlength (rows)) = count_pre)) (PreH9 : ((Zlength (lens)) = count_pre)) (PreH10 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) lens)) (PreH12 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens)) (PreH13 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH14 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows) (lens)))) (PreH16 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows) (lens)))) (PreH17 : (FlatRows flat rows count_pre number_width_pre)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "result_length" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "result" ) )) # Ptr |-> (result_pre))
  ** ((( &( "count" ) )) # Int |-> (count_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat)
  ** (intArray.full lengths_pre count_pre lens)
  ** (intArray.undef_full result_pre (sum (lens)))
|--
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= count_pre) ” &&
  “ ((-1) <= (count_pre - 1)) ” &&
  “ ((count_pre - 1) < count_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ ((Zlength (rows)) = count_pre) ” &&
  “ ((Zlength (lens)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows) (lens))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows) (lens))) ” &&
  “ (FlatRows flat rows count_pre number_width_pre) ”

noncomputable def concatenating_numbers_partial_solve_wit_1_aux : Prop :=
  forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (count_pre > 1)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : ((Zlength (rows)) = count_pre)) (PreH9 : ((Zlength (lens)) = count_pre)) (PreH10 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) lens)) (PreH12 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens)) (PreH13 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH14 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows)))) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows) (lens)))) (PreH16 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows) (lens)))) (PreH17 : (FlatRows flat rows count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat)
  ** (intArray.full lengths_pre count_pre lens)
  ** (intArray.undef_full result_pre (sum (lens)))
|--
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= count_pre) ” &&
  “ ((-1) <= (count_pre - 1)) ” &&
  “ ((count_pre - 1) < count_pre) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ ((Zlength (rows)) = count_pre) ” &&
  “ ((Zlength (lens)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows) (lens))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows) (lens))) ” &&
  “ (FlatRows flat rows count_pre number_width_pre) ” &&
  “ (count_pre > 1) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ ((Zlength (rows)) = count_pre) ” &&
  “ ((Zlength (lens)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows) (lens))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows) (lens))) ” &&
  “ (FlatRows flat rows count_pre number_width_pre) ”
  &&  (intArray.full numbers_pre (count_pre * number_width_pre) flat)
  ** (intArray.full lengths_pre count_pre lens)
  ** (intArray.undef_full result_pre (sum (lens)))

noncomputable def concatenating_numbers_partial_solve_wit_1 : Prop := concatenating_numbers_partial_solve_wit_1_pure -> concatenating_numbers_partial_solve_wit_1_aux

noncomputable def concatenating_numbers_partial_solve_wit_2 : Prop :=
  forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (output : (List Int)) (rows1 : (List (List Int))) (result_length : Int) (lens1 : (List Int)) (j : Int) (i : Int) (PreH1 : ((0 : Int) <= (i * number_width_pre))) (PreH2 : (((i * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH3 : ((j < (Znth (i) (lens1) ((0 : Int)))) -> (result_length < (sum (lens))))) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : (1 <= (sum (lens)))) (PreH9 : ((sum (lens)) <= 200)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < count_pre)) (PreH12 : ((0 : Int) <= j)) (PreH13 : (j <= (Znth (i) (lens1) ((0 : Int))))) (PreH14 : (1 <= (Znth (i) (lens1) ((0 : Int))))) (PreH15 : ((Znth (i) (lens1) ((0 : Int))) <= number_width_pre)) (PreH16 : ((Zlength (rows1)) = count_pre)) (PreH17 : ((Zlength (lens1)) = count_pre)) (PreH18 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH19 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH20 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH21 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH22 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH23 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH24 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH25 : (PairedPermutation rows rows1 lens lens1)) (PreH26 : (GreedySorted rows1 lens1)) (PreH27 : ((sum (lens1)) = (sum (lens)))) (PreH28 : (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j)))) (PreH29 : (result_length = (Zlength (output)))) (PreH30 : ((0 : Int) <= result_length)) (PreH31 : (result_length <= (sum (lens)))) (PreH32 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** (intArray.seg result_pre (0 : Int) result_length output)
  ** (intArray.undef_seg result_pre result_length (sum (lens)))
|--
  “ ((0 : Int) <= (i * number_width_pre)) ” &&
  “ (((i * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((j < (Znth (i) (lens1) ((0 : Int)))) -> (result_length < (sum (lens)))) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < count_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (Znth (i) (lens1) ((0 : Int)))) ” &&
  “ (1 <= (Znth (i) (lens1) ((0 : Int)))) ” &&
  “ ((Znth (i) (lens1) ((0 : Int))) <= number_width_pre) ” &&
  “ ((Zlength (rows1)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1))) ” &&
  “ (PairedPermutation rows rows1 lens lens1) ” &&
  “ (GreedySorted rows1 lens1) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j))) ” &&
  “ (result_length = (Zlength (output))) ” &&
  “ ((0 : Int) <= result_length) ” &&
  “ (result_length <= (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (((lengths_pre + (i * sizeof(INT)))) # Int |-> ((Znth i lens1 (0 : Int))))
  ** (intArray.missing_i lengths_pre i (0 : Int) count_pre lens1)
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.seg result_pre (0 : Int) result_length output)
  ** (intArray.undef_seg result_pre result_length (sum (lens)))

noncomputable def concatenating_numbers_partial_solve_wit_3 : Prop :=
  forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (output : (List Int)) (rows1 : (List (List Int))) (result_length : Int) (lens1 : (List Int)) (j : Int) (i : Int) (PreH1 : (j < (Znth i lens1 (0 : Int)))) (PreH2 : ((0 : Int) <= (i * number_width_pre))) (PreH3 : (((i * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((j < (Znth (i) (lens1) ((0 : Int)))) -> (result_length < (sum (lens))))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < count_pre)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= (Znth (i) (lens1) ((0 : Int))))) (PreH15 : (1 <= (Znth (i) (lens1) ((0 : Int))))) (PreH16 : ((Znth (i) (lens1) ((0 : Int))) <= number_width_pre)) (PreH17 : ((Zlength (rows1)) = count_pre)) (PreH18 : ((Zlength (lens1)) = count_pre)) (PreH19 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH20 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH21 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH23 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH24 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH25 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH26 : (PairedPermutation rows rows1 lens lens1)) (PreH27 : (GreedySorted rows1 lens1)) (PreH28 : ((sum (lens1)) = (sum (lens)))) (PreH29 : (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j)))) (PreH30 : (result_length = (Zlength (output)))) (PreH31 : ((0 : Int) <= result_length)) (PreH32 : (result_length <= (sum (lens)))) (PreH33 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full lengths_pre count_pre lens1)
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.seg result_pre (0 : Int) result_length output)
  ** (intArray.undef_seg result_pre result_length (sum (lens)))
|--
  “ (j < (Znth i lens1 (0 : Int))) ” &&
  “ ((0 : Int) <= (i * number_width_pre)) ” &&
  “ (((i * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((j < (Znth (i) (lens1) ((0 : Int)))) -> (result_length < (sum (lens)))) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < count_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (Znth (i) (lens1) ((0 : Int)))) ” &&
  “ (1 <= (Znth (i) (lens1) ((0 : Int)))) ” &&
  “ ((Znth (i) (lens1) ((0 : Int))) <= number_width_pre) ” &&
  “ ((Zlength (rows1)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1))) ” &&
  “ (PairedPermutation rows rows1 lens lens1) ” &&
  “ (GreedySorted rows1 lens1) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j))) ” &&
  “ (result_length = (Zlength (output))) ” &&
  “ ((0 : Int) <= result_length) ” &&
  “ (result_length <= (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (((numbers_pre + (((i * number_width_pre) + j) * sizeof(INT)))) # Int |-> ((Znth ((i * number_width_pre) + j) flat1 (0 : Int))))
  ** (intArray.missing_i numbers_pre ((i * number_width_pre) + j) (0 : Int) (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** (intArray.seg result_pre (0 : Int) result_length output)
  ** (intArray.undef_seg result_pre result_length (sum (lens)))

noncomputable def concatenating_numbers_partial_solve_wit_4 : Prop :=
  forall (result_pre : Int) (lengths_pre : Int) (number_width_pre : Int) (count_pre : Int) (numbers_pre : Int) (lens : (List Int)) (rows : (List (List Int))) (flat1 : (List Int)) (output : (List Int)) (rows1 : (List (List Int))) (result_length : Int) (lens1 : (List Int)) (j : Int) (i : Int) (PreH1 : (j < (Znth i lens1 (0 : Int)))) (PreH2 : ((0 : Int) <= (i * number_width_pre))) (PreH3 : (((i * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre))) (PreH4 : ((j < (Znth (i) (lens1) ((0 : Int)))) -> (result_length < (sum (lens))))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < count_pre)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= (Znth (i) (lens1) ((0 : Int))))) (PreH15 : (1 <= (Znth (i) (lens1) ((0 : Int))))) (PreH16 : ((Znth (i) (lens1) ((0 : Int))) <= number_width_pre)) (PreH17 : ((Zlength (rows1)) = count_pre)) (PreH18 : ((Zlength (lens1)) = count_pre)) (PreH19 : (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1)))) (PreH20 : (Forall ((LE.le (α := Int)) (1)) lens1)) (PreH21 : (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH23 : (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1)))) (PreH24 : (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1)))) (PreH25 : (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1)))) (PreH26 : (PairedPermutation rows rows1 lens lens1)) (PreH27 : (GreedySorted rows1 lens1)) (PreH28 : ((sum (lens1)) = (sum (lens)))) (PreH29 : (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j)))) (PreH30 : (result_length = (Zlength (output)))) (PreH31 : ((0 : Int) <= result_length)) (PreH32 : (result_length <= (sum (lens)))) (PreH33 : (FlatRows flat1 rows1 count_pre number_width_pre)) ,
  (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** (intArray.seg result_pre (0 : Int) result_length output)
  ** (intArray.undef_seg result_pre result_length (sum (lens)))
|--
  “ (j < (Znth i lens1 (0 : Int))) ” &&
  “ ((0 : Int) <= (i * number_width_pre)) ” &&
  “ (((i * number_width_pre) + number_width_pre) <= (count_pre * number_width_pre)) ” &&
  “ ((j < (Znth (i) (lens1) ((0 : Int)))) -> (result_length < (sum (lens)))) ” &&
  “ (1 <= count_pre) ” &&
  “ (count_pre <= 20) ” &&
  “ (1 <= number_width_pre) ” &&
  “ (number_width_pre <= 10) ” &&
  “ (1 <= (sum (lens))) ” &&
  “ ((sum (lens)) <= 200) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < count_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (Znth (i) (lens1) ((0 : Int)))) ” &&
  “ (1 <= (Znth (i) (lens1) ((0 : Int)))) ” &&
  “ ((Znth (i) (lens1) ((0 : Int))) <= number_width_pre) ” &&
  “ ((Zlength (rows1)) = count_pre) ” &&
  “ ((Zlength (lens1)) = count_pre) ” &&
  “ (Forall (Eq (number_width_pre)) (List.map (Zlength) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) lens1) ” &&
  “ (Forall ((GE.ge (α := Int)) (number_width_pre)) lens1) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (List.map ((hd ((0 : Int)))) (rows1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (concatenate_rows (rows1) (lens1))) ” &&
  “ (Forall ((GE.ge (α := Int)) (9)) (concatenate_rows (rows1) (lens1))) ” &&
  “ (PairedPermutation rows rows1 lens lens1) ” &&
  “ (GreedySorted rows1 lens1) ” &&
  “ ((sum (lens1)) = (sum (lens))) ” &&
  “ (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j))) ” &&
  “ (result_length = (Zlength (output))) ” &&
  “ ((0 : Int) <= result_length) ” &&
  “ (result_length <= (sum (lens))) ” &&
  “ (FlatRows flat1 rows1 count_pre number_width_pre) ”
  &&  (((result_pre + (result_length * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg result_pre (result_length + 1) (sum (lens)))
  ** (intArray.full numbers_pre (count_pre * number_width_pre) flat1)
  ** (intArray.full lengths_pre count_pre lens1)
  ** (intArray.seg result_pre (0 : Int) result_length output)


structure VC_Correct : Type where
  proof_of_quicksort_numbers_safety_wit_1 : quicksort_numbers_safety_wit_1
  proof_of_quicksort_numbers_safety_wit_2 : quicksort_numbers_safety_wit_2
  proof_of_quicksort_numbers_safety_wit_3 : quicksort_numbers_safety_wit_3
  proof_of_quicksort_numbers_safety_wit_4 : quicksort_numbers_safety_wit_4
  proof_of_quicksort_numbers_safety_wit_5 : quicksort_numbers_safety_wit_5
  proof_of_quicksort_numbers_safety_wit_7 : quicksort_numbers_safety_wit_7
  proof_of_quicksort_numbers_safety_wit_8 : quicksort_numbers_safety_wit_8
  proof_of_quicksort_numbers_safety_wit_9 : quicksort_numbers_safety_wit_9
  proof_of_quicksort_numbers_safety_wit_10 : quicksort_numbers_safety_wit_10
  proof_of_quicksort_numbers_safety_wit_11 : quicksort_numbers_safety_wit_11
  proof_of_quicksort_numbers_safety_wit_12 : quicksort_numbers_safety_wit_12
  proof_of_quicksort_numbers_safety_wit_13 : quicksort_numbers_safety_wit_13
  proof_of_quicksort_numbers_safety_wit_14 : quicksort_numbers_safety_wit_14
  proof_of_quicksort_numbers_safety_wit_15 : quicksort_numbers_safety_wit_15
  proof_of_quicksort_numbers_safety_wit_16 : quicksort_numbers_safety_wit_16
  proof_of_quicksort_numbers_safety_wit_17 : quicksort_numbers_safety_wit_17
  proof_of_quicksort_numbers_safety_wit_18 : quicksort_numbers_safety_wit_18
  proof_of_quicksort_numbers_safety_wit_20 : quicksort_numbers_safety_wit_20
  proof_of_quicksort_numbers_safety_wit_21 : quicksort_numbers_safety_wit_21
  proof_of_quicksort_numbers_safety_wit_22 : quicksort_numbers_safety_wit_22
  proof_of_quicksort_numbers_safety_wit_23 : quicksort_numbers_safety_wit_23
  proof_of_quicksort_numbers_safety_wit_24 : quicksort_numbers_safety_wit_24
  proof_of_quicksort_numbers_safety_wit_25 : quicksort_numbers_safety_wit_25
  proof_of_quicksort_numbers_safety_wit_26 : quicksort_numbers_safety_wit_26
  proof_of_quicksort_numbers_safety_wit_27 : quicksort_numbers_safety_wit_27
  proof_of_quicksort_numbers_safety_wit_28 : quicksort_numbers_safety_wit_28
  proof_of_quicksort_numbers_safety_wit_29 : quicksort_numbers_safety_wit_29
  proof_of_quicksort_numbers_safety_wit_30 : quicksort_numbers_safety_wit_30
  proof_of_quicksort_numbers_safety_wit_31 : quicksort_numbers_safety_wit_31
  proof_of_quicksort_numbers_safety_wit_32 : quicksort_numbers_safety_wit_32
  proof_of_quicksort_numbers_safety_wit_33 : quicksort_numbers_safety_wit_33
  proof_of_quicksort_numbers_safety_wit_34 : quicksort_numbers_safety_wit_34
  proof_of_quicksort_numbers_safety_wit_35 : quicksort_numbers_safety_wit_35
  proof_of_quicksort_numbers_safety_wit_36 : quicksort_numbers_safety_wit_36
  proof_of_quicksort_numbers_safety_wit_37 : quicksort_numbers_safety_wit_37
  proof_of_quicksort_numbers_safety_wit_38 : quicksort_numbers_safety_wit_38
  proof_of_quicksort_numbers_safety_wit_39 : quicksort_numbers_safety_wit_39
  proof_of_quicksort_numbers_safety_wit_40 : quicksort_numbers_safety_wit_40
  proof_of_quicksort_numbers_safety_wit_41 : quicksort_numbers_safety_wit_41
  proof_of_quicksort_numbers_safety_wit_42 : quicksort_numbers_safety_wit_42
  proof_of_quicksort_numbers_safety_wit_43 : quicksort_numbers_safety_wit_43
  proof_of_quicksort_numbers_safety_wit_44 : quicksort_numbers_safety_wit_44
  proof_of_quicksort_numbers_safety_wit_45 : quicksort_numbers_safety_wit_45
  proof_of_quicksort_numbers_safety_wit_46 : quicksort_numbers_safety_wit_46
  proof_of_quicksort_numbers_safety_wit_47 : quicksort_numbers_safety_wit_47
  proof_of_quicksort_numbers_safety_wit_48 : quicksort_numbers_safety_wit_48
  proof_of_quicksort_numbers_safety_wit_49 : quicksort_numbers_safety_wit_49
  proof_of_quicksort_numbers_safety_wit_50 : quicksort_numbers_safety_wit_50
  proof_of_quicksort_numbers_safety_wit_51 : quicksort_numbers_safety_wit_51
  proof_of_quicksort_numbers_safety_wit_52 : quicksort_numbers_safety_wit_52
  proof_of_quicksort_numbers_partial_solve_wit_1 : quicksort_numbers_partial_solve_wit_1
  proof_of_quicksort_numbers_partial_solve_wit_2 : quicksort_numbers_partial_solve_wit_2
  proof_of_quicksort_numbers_partial_solve_wit_3 : quicksort_numbers_partial_solve_wit_3
  proof_of_quicksort_numbers_partial_solve_wit_4 : quicksort_numbers_partial_solve_wit_4
  proof_of_quicksort_numbers_partial_solve_wit_5 : quicksort_numbers_partial_solve_wit_5
  proof_of_quicksort_numbers_partial_solve_wit_6 : quicksort_numbers_partial_solve_wit_6
  proof_of_quicksort_numbers_partial_solve_wit_7 : quicksort_numbers_partial_solve_wit_7
  proof_of_quicksort_numbers_partial_solve_wit_8 : quicksort_numbers_partial_solve_wit_8
  proof_of_quicksort_numbers_partial_solve_wit_9 : quicksort_numbers_partial_solve_wit_9
  proof_of_quicksort_numbers_partial_solve_wit_10 : quicksort_numbers_partial_solve_wit_10
  proof_of_quicksort_numbers_partial_solve_wit_11 : quicksort_numbers_partial_solve_wit_11
  proof_of_quicksort_numbers_partial_solve_wit_12 : quicksort_numbers_partial_solve_wit_12
  proof_of_quicksort_numbers_partial_solve_wit_13 : quicksort_numbers_partial_solve_wit_13
  proof_of_quicksort_numbers_partial_solve_wit_14 : quicksort_numbers_partial_solve_wit_14
  proof_of_quicksort_numbers_partial_solve_wit_15 : quicksort_numbers_partial_solve_wit_15
  proof_of_quicksort_numbers_partial_solve_wit_16 : quicksort_numbers_partial_solve_wit_16
  proof_of_quicksort_numbers_partial_solve_wit_17 : quicksort_numbers_partial_solve_wit_17
  proof_of_quicksort_numbers_partial_solve_wit_18 : quicksort_numbers_partial_solve_wit_18
  proof_of_quicksort_numbers_partial_solve_wit_19 : quicksort_numbers_partial_solve_wit_19
  proof_of_quicksort_numbers_partial_solve_wit_20 : quicksort_numbers_partial_solve_wit_20
  proof_of_quicksort_numbers_partial_solve_wit_21 : quicksort_numbers_partial_solve_wit_21
  proof_of_quicksort_numbers_partial_solve_wit_22_pure : quicksort_numbers_partial_solve_wit_22_pure
  proof_of_quicksort_numbers_partial_solve_wit_22 : quicksort_numbers_partial_solve_wit_22
  proof_of_quicksort_numbers_partial_solve_wit_23 : quicksort_numbers_partial_solve_wit_23
  proof_of_quicksort_numbers_partial_solve_wit_24_pure : quicksort_numbers_partial_solve_wit_24_pure
  proof_of_quicksort_numbers_partial_solve_wit_24 : quicksort_numbers_partial_solve_wit_24
  proof_of_concatenating_numbers_safety_wit_1 : concatenating_numbers_safety_wit_1
  proof_of_concatenating_numbers_safety_wit_2 : concatenating_numbers_safety_wit_2
  proof_of_concatenating_numbers_safety_wit_3 : concatenating_numbers_safety_wit_3
  proof_of_concatenating_numbers_safety_wit_4 : concatenating_numbers_safety_wit_4
  proof_of_concatenating_numbers_safety_wit_5 : concatenating_numbers_safety_wit_5
  proof_of_concatenating_numbers_safety_wit_6 : concatenating_numbers_safety_wit_6
  proof_of_concatenating_numbers_safety_wit_7 : concatenating_numbers_safety_wit_7
  proof_of_concatenating_numbers_safety_wit_8 : concatenating_numbers_safety_wit_8
  proof_of_concatenating_numbers_safety_wit_9 : concatenating_numbers_safety_wit_9
  proof_of_concatenating_numbers_safety_wit_10 : concatenating_numbers_safety_wit_10
  proof_of_concatenating_numbers_safety_wit_11 : concatenating_numbers_safety_wit_11
  proof_of_concatenating_numbers_safety_wit_12 : concatenating_numbers_safety_wit_12
  proof_of_concatenating_numbers_safety_wit_13 : concatenating_numbers_safety_wit_13
  proof_of_concatenating_numbers_partial_solve_wit_1_pure : concatenating_numbers_partial_solve_wit_1_pure
  proof_of_concatenating_numbers_partial_solve_wit_1 : concatenating_numbers_partial_solve_wit_1
  proof_of_concatenating_numbers_partial_solve_wit_2 : concatenating_numbers_partial_solve_wit_2
  proof_of_concatenating_numbers_partial_solve_wit_3 : concatenating_numbers_partial_solve_wit_3
  proof_of_concatenating_numbers_partial_solve_wit_4 : concatenating_numbers_partial_solve_wit_4
  proof_of_quicksort_numbers_safety_wit_6 : quicksort_numbers_safety_wit_6
  proof_of_quicksort_numbers_safety_wit_19 : quicksort_numbers_safety_wit_19
  proof_of_quicksort_numbers_entail_wit_1 : quicksort_numbers_entail_wit_1
  proof_of_quicksort_numbers_entail_wit_2 : quicksort_numbers_entail_wit_2
  proof_of_quicksort_numbers_entail_wit_3_1 : quicksort_numbers_entail_wit_3_1
  proof_of_quicksort_numbers_entail_wit_3_2 : quicksort_numbers_entail_wit_3_2
  proof_of_quicksort_numbers_entail_wit_4_1 : quicksort_numbers_entail_wit_4_1
  proof_of_quicksort_numbers_entail_wit_4_2 : quicksort_numbers_entail_wit_4_2
  proof_of_quicksort_numbers_entail_wit_5 : quicksort_numbers_entail_wit_5
  proof_of_quicksort_numbers_entail_wit_6_1 : quicksort_numbers_entail_wit_6_1
  proof_of_quicksort_numbers_entail_wit_6_2 : quicksort_numbers_entail_wit_6_2
  proof_of_quicksort_numbers_entail_wit_7 : quicksort_numbers_entail_wit_7
  proof_of_quicksort_numbers_entail_wit_8 : quicksort_numbers_entail_wit_8
  proof_of_quicksort_numbers_entail_wit_9_1 : quicksort_numbers_entail_wit_9_1
  proof_of_quicksort_numbers_entail_wit_9_2 : quicksort_numbers_entail_wit_9_2
  proof_of_quicksort_numbers_entail_wit_10 : quicksort_numbers_entail_wit_10
  proof_of_quicksort_numbers_entail_wit_11 : quicksort_numbers_entail_wit_11
  proof_of_quicksort_numbers_entail_wit_12 : quicksort_numbers_entail_wit_12
  proof_of_quicksort_numbers_entail_wit_13 : quicksort_numbers_entail_wit_13
  proof_of_quicksort_numbers_return_wit_1 : quicksort_numbers_return_wit_1
  proof_of_quicksort_numbers_return_wit_2 : quicksort_numbers_return_wit_2
  proof_of_quicksort_numbers_return_wit_3 : quicksort_numbers_return_wit_3
  proof_of_quicksort_numbers_return_wit_4 : quicksort_numbers_return_wit_4
  proof_of_quicksort_numbers_partial_solve_wit_23_pure : quicksort_numbers_partial_solve_wit_23_pure
  proof_of_concatenating_numbers_entail_wit_1 : concatenating_numbers_entail_wit_1
  proof_of_concatenating_numbers_entail_wit_2_1 : concatenating_numbers_entail_wit_2_1
  proof_of_concatenating_numbers_entail_wit_2_2 : concatenating_numbers_entail_wit_2_2
  proof_of_concatenating_numbers_entail_wit_3 : concatenating_numbers_entail_wit_3
  proof_of_concatenating_numbers_entail_wit_4 : concatenating_numbers_entail_wit_4
  proof_of_concatenating_numbers_entail_wit_5 : concatenating_numbers_entail_wit_5
  proof_of_concatenating_numbers_return_wit_1 : concatenating_numbers_return_wit_1

end SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_goal
