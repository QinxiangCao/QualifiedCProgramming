import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.bucket_sort.bucket_sort_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.bucket_sort.bucket_sort_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance bucket_sort_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH4 : (Forall ((GE.ge (α := Int)) (999999999)) input)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre input)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def sort_safety_wit_2 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (PreH1 : (n_pre > 1)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH5 : (Forall ((GE.ge (α := Int)) (999999999)) input)) ,
  ((( &( "max_value" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre input)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def sort_safety_wit_3 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (PreH1 : (n_pre > 1)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH5 : (Forall ((GE.ge (α := Int)) (999999999)) input)) ,
  ((( &( "i" ) )) # Int |->_)
  ** (intArray.full a_pre n_pre input)
  ** ((( &( "max_value" ) )) # Int |-> ((Znth (0 : Int) input (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def sort_safety_wit_4 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (max_value : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) > max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GE.ge (α := Int)) (999999999)) input)) (PreH11 : (PrefixMaximum input i max_value)) ,
  (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "max_value" ) )) # Int |-> ((Znth i input (0 : Int))))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def sort_safety_wit_5 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (max_value : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) <= max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GE.ge (α := Int)) (999999999)) input)) (PreH11 : (PrefixMaximum input i max_value)) ,
  (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def sort_safety_wit_6 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (max_value : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((0 : Int) <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH9 : (Forall ((GE.ge (α := Int)) (999999999)) input)) (PreH10 : (PrefixMaximum input i max_value)) ,
  ((( &( "exponent" ) )) # Int |->_)
  ** (intArray.undef_full ( &( "count" ) ) 10)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** (intArray.full a_pre n_pre input)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def sort_safety_wit_7 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (current : (List Int)) (exponent : Int) (max_value : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= max_value)) (PreH4 : (max_value <= 999999999)) (PreH5 : (1 <= exponent)) (PreH6 : (exponent <= 1000000000)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH8 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH9 : (PrefixMaximum input n_pre max_value)) (PreH10 : (DecimalExponent exponent)) (PreH11 : (RadixPassState input current exponent)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
  ** (intArray.undef_full ( &( "count" ) ) 10)
|--
  “ ((max_value ≠ (INT_MIN)) ∨ (exponent ≠ (-1))) ” &&
  “ (exponent ≠ (0 : Int)) ”

noncomputable def sort_safety_wit_8 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (current : (List Int)) (exponent : Int) (max_value : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= max_value)) (PreH4 : (max_value <= 999999999)) (PreH5 : (1 <= exponent)) (PreH6 : (exponent <= 1000000000)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH8 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH9 : (PrefixMaximum input n_pre max_value)) (PreH10 : (DecimalExponent exponent)) (PreH11 : (RadixPassState input current exponent)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
  ** (intArray.undef_full ( &( "count" ) ) 10)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def sort_safety_wit_9 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (current : (List Int)) (exponent : Int) (max_value : Int) (PreH1 : ((Z.quot max_value exponent) > (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 1000000000)) (PreH8 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH9 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH10 : (PrefixMaximum input n_pre max_value)) (PreH11 : (DecimalExponent exponent)) (PreH12 : (RadixPassState input current exponent)) ,
  ((( &( "digit" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
  ** (intArray.undef_full ( &( "count" ) ) 10)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def sort_safety_wit_10 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (zero_prefix : (List Int)) (current : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= max_value)) (PreH4 : (max_value <= 999999999)) (PreH5 : (1 <= exponent)) (PreH6 : (exponent <= 100000000)) (PreH7 : ((0 : Int) < (Z.quot max_value exponent))) (PreH8 : ((0 : Int) <= digit)) (PreH9 : (digit <= 10)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH11 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH12 : (Forall (Eq ((0 : Int))) zero_prefix)) (PreH13 : (PrefixMaximum input n_pre max_value)) (PreH14 : (DecimalExponent exponent)) (PreH15 : (RadixPassState input current exponent)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "digit" ) )) # Int |-> (digit))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.seg ( &( "count" ) ) (0 : Int) digit zero_prefix)
  ** (intArray.undef_seg ( &( "count" ) ) digit 10)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (10 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 10) ”

noncomputable def sort_safety_wit_11 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (zero_prefix : (List Int)) (current : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : ((0 : Int) < (Z.quot max_value exponent))) (PreH9 : ((0 : Int) <= digit)) (PreH10 : (digit <= 10)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH13 : (Forall (Eq ((0 : Int))) zero_prefix)) (PreH14 : (PrefixMaximum input n_pre max_value)) (PreH15 : (DecimalExponent exponent)) (PreH16 : (RadixPassState input current exponent)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "digit" ) )) # Int |-> (digit))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.seg ( &( "count" ) ) (0 : Int) digit zero_prefix)
  ** (intArray.undef_seg ( &( "count" ) ) digit 10)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def sort_safety_wit_12 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (zero_prefix : (List Int)) (current : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : ((0 : Int) < (Z.quot max_value exponent))) (PreH9 : ((0 : Int) <= digit)) (PreH10 : (digit <= 10)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH13 : (Forall (Eq ((0 : Int))) zero_prefix)) (PreH14 : (PrefixMaximum input n_pre max_value)) (PreH15 : (DecimalExponent exponent)) (PreH16 : (RadixPassState input current exponent)) ,
  (intArray.seg ( &( "count" ) ) (0 : Int) (digit + 1) (zero_prefix ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "count" ) ) (digit + 1) 10)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "digit" ) )) # Int |-> (digit))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ ((digit + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (digit + 1)) ”

noncomputable def sort_safety_wit_13 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (zero_prefix : (List Int)) (current : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (PreH1 : (digit >= 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : ((0 : Int) < (Z.quot max_value exponent))) (PreH9 : ((0 : Int) <= digit)) (PreH10 : (digit <= 10)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH13 : (Forall (Eq ((0 : Int))) zero_prefix)) (PreH14 : (PrefixMaximum input n_pre max_value)) (PreH15 : (DecimalExponent exponent)) (PreH16 : (RadixPassState input current exponent)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.seg ( &( "count" ) ) (0 : Int) digit zero_prefix)
  ** (intArray.undef_seg ( &( "count" ) ) digit 10)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def sort_safety_wit_14 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (counts : (List Int)) (current : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : ((0 : Int) < (Z.quot max_value exponent))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts)) (PreH14 : (Forall ((GE.ge (α := Int)) (i)) counts)) (PreH15 : (PrefixMaximum input n_pre max_value)) (PreH16 : (DecimalExponent exponent)) (PreH17 : (RadixPassState input current exponent)) (PreH18 : (DigitHistogramPrefix current exponent i counts)) ,
  (intArray.full a_pre n_pre current)
  ** ((( &( "digit" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full ( &( "count" ) ) 10 counts)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (((Z.quot (Znth i current (0 : Int)) exponent) ≠ (INT_MIN)) ∨ (10 ≠ (-1))) ” &&
  “ (10 ≠ (0 : Int)) ”

noncomputable def sort_safety_wit_15 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (counts : (List Int)) (current : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : ((0 : Int) < (Z.quot max_value exponent))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts)) (PreH14 : (Forall ((GE.ge (α := Int)) (i)) counts)) (PreH15 : (PrefixMaximum input n_pre max_value)) (PreH16 : (DecimalExponent exponent)) (PreH17 : (RadixPassState input current exponent)) (PreH18 : (DigitHistogramPrefix current exponent i counts)) ,
  (intArray.full a_pre n_pre current)
  ** ((( &( "digit" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full ( &( "count" ) ) 10 counts)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (((Znth i current (0 : Int)) ≠ (INT_MIN)) ∨ (exponent ≠ (-1))) ” &&
  “ (exponent ≠ (0 : Int)) ”

noncomputable def sort_safety_wit_16 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (counts : (List Int)) (current : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : ((0 : Int) < (Z.quot max_value exponent))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts)) (PreH14 : (Forall ((GE.ge (α := Int)) (i)) counts)) (PreH15 : (PrefixMaximum input n_pre max_value)) (PreH16 : (DecimalExponent exponent)) (PreH17 : (RadixPassState input current exponent)) (PreH18 : (DigitHistogramPrefix current exponent i counts)) ,
  (intArray.full a_pre n_pre current)
  ** ((( &( "digit" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full ( &( "count" ) ) 10 counts)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (10 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 10) ”

noncomputable def sort_safety_wit_17 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (current : (List Int)) (counts : (List Int)) (max_value : Int) (exponent : Int) (i : Int) (digit : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= max_value)) (PreH4 : (max_value <= 999999999)) (PreH5 : (1 <= exponent)) (PreH6 : (exponent <= 100000000)) (PreH7 : ((0 : Int) < (Z.quot max_value exponent))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH11 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts)) (PreH13 : (Forall ((GE.ge (α := Int)) (i)) counts)) (PreH14 : (PrefixMaximum input n_pre max_value)) (PreH15 : (DecimalExponent exponent)) (PreH16 : (RadixPassState input current exponent)) (PreH17 : (DigitHistogramPrefix current exponent i counts)) (PreH18 : (digit = (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10))) (PreH19 : ((0 : Int) <= digit)) (PreH20 : (digit < 10)) ,
  (intArray.full ( &( "count" ) ) 10 counts)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "digit" ) )) # Int |-> (digit))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (((Znth digit counts (0 : Int)) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth digit counts (0 : Int)) + 1)) ”
) \/
(
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (current : (List Int)) (counts : (List Int)) (max_value : Int) (exponent : Int) (i : Int) (digit : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= max_value)) (PreH4 : (max_value <= 999999999)) (PreH5 : (1 <= exponent)) (PreH6 : (exponent <= 100000000)) (PreH7 : ((0 : Int) < (Z.quot max_value exponent))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH11 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts)) (PreH13 : (Forall ((GE.ge (α := Int)) (i)) counts)) (PreH14 : (PrefixMaximum input n_pre max_value)) (PreH15 : (DecimalExponent exponent)) (PreH16 : (RadixPassState input current exponent)) (PreH17 : (DigitHistogramPrefix current exponent i counts)) (PreH18 : (digit = (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10))) (PreH19 : ((0 : Int) <= digit)) (PreH20 : (digit < 10)) ,
  (intArray.full ( &( "count" ) ) 10 counts)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "digit" ) )) # Int |-> (digit))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (((Znth digit counts (0 : Int)) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth digit counts (0 : Int)) + 1)) ”
)

noncomputable def sort_safety_wit_17_split_goal_1 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (current : (List Int)) (counts : (List Int)) (max_value : Int) (exponent : Int) (i : Int) (digit : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= max_value)) (PreH4 : (max_value <= 999999999)) (PreH5 : (1 <= exponent)) (PreH6 : (exponent <= 100000000)) (PreH7 : ((0 : Int) < (Z.quot max_value exponent))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH11 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts)) (PreH13 : (Forall ((GE.ge (α := Int)) (i)) counts)) (PreH14 : (PrefixMaximum input n_pre max_value)) (PreH15 : (DecimalExponent exponent)) (PreH16 : (RadixPassState input current exponent)) (PreH17 : (DigitHistogramPrefix current exponent i counts)) (PreH18 : (digit = (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10))) (PreH19 : ((0 : Int) <= digit)) (PreH20 : (digit < 10)) ,
  (intArray.full ( &( "count" ) ) 10 counts)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "digit" ) )) # Int |-> (digit))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (((Znth digit counts (0 : Int)) + 1) <= INT_MAX) ”

noncomputable def sort_safety_wit_17_split_goal_2 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (current : (List Int)) (counts : (List Int)) (max_value : Int) (exponent : Int) (i : Int) (digit : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= max_value)) (PreH4 : (max_value <= 999999999)) (PreH5 : (1 <= exponent)) (PreH6 : (exponent <= 100000000)) (PreH7 : ((0 : Int) < (Z.quot max_value exponent))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH11 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts)) (PreH13 : (Forall ((GE.ge (α := Int)) (i)) counts)) (PreH14 : (PrefixMaximum input n_pre max_value)) (PreH15 : (DecimalExponent exponent)) (PreH16 : (RadixPassState input current exponent)) (PreH17 : (DigitHistogramPrefix current exponent i counts)) (PreH18 : (digit = (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10))) (PreH19 : ((0 : Int) <= digit)) (PreH20 : (digit < 10)) ,
  (intArray.full ( &( "count" ) ) 10 counts)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "digit" ) )) # Int |-> (digit))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ ((INT_MIN) <= ((Znth digit counts (0 : Int)) + 1)) ”

noncomputable def sort_safety_wit_18 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (current : (List Int)) (counts : (List Int)) (max_value : Int) (exponent : Int) (i : Int) (digit : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= max_value)) (PreH4 : (max_value <= 999999999)) (PreH5 : (1 <= exponent)) (PreH6 : (exponent <= 100000000)) (PreH7 : ((0 : Int) < (Z.quot max_value exponent))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH11 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts)) (PreH13 : (Forall ((GE.ge (α := Int)) (i)) counts)) (PreH14 : (PrefixMaximum input n_pre max_value)) (PreH15 : (DecimalExponent exponent)) (PreH16 : (RadixPassState input current exponent)) (PreH17 : (DigitHistogramPrefix current exponent i counts)) (PreH18 : (digit = (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10))) (PreH19 : ((0 : Int) <= digit)) (PreH20 : (digit < 10)) ,
  (intArray.full ( &( "count" ) ) 10 (replace_Znth (digit) (((Znth digit counts (0 : Int)) + 1)) (counts)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def sort_safety_wit_19 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (counts : (List Int)) (current : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : ((0 : Int) < (Z.quot max_value exponent))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts)) (PreH14 : (Forall ((GE.ge (α := Int)) (i)) counts)) (PreH15 : (PrefixMaximum input n_pre max_value)) (PreH16 : (DecimalExponent exponent)) (PreH17 : (RadixPassState input current exponent)) (PreH18 : (DigitHistogramPrefix current exponent i counts)) ,
  ((( &( "digit" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 counts)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def sort_safety_wit_20 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (totals : (List Int)) (current : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (histogram : (List Int)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (histogram)) = 10)) (PreH4 : ((0 : Int) <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : ((0 : Int) < (Z.quot max_value exponent))) (PreH9 : (1 <= digit)) (PreH10 : (digit <= 10)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) histogram)) (PreH14 : (Forall ((GE.ge (α := Int)) (n_pre)) histogram)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) totals)) (PreH16 : (Forall ((GE.ge (α := Int)) (n_pre)) totals)) (PreH17 : (PrefixMaximum input n_pre max_value)) (PreH18 : (DecimalExponent exponent)) (PreH19 : (RadixPassState input current exponent)) (PreH20 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH21 : (DigitPrefixTotals histogram totals digit)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "digit" ) )) # Int |-> (digit))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 totals)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (10 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 10) ”

noncomputable def sort_safety_wit_21 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (totals : (List Int)) (current : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (histogram : (List Int)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) < (Z.quot max_value exponent))) (PreH10 : (1 <= digit)) (PreH11 : (digit <= 10)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH13 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) histogram)) (PreH15 : (Forall ((GE.ge (α := Int)) (n_pre)) histogram)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) totals)) (PreH17 : (Forall ((GE.ge (α := Int)) (n_pre)) totals)) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current exponent)) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH22 : (DigitPrefixTotals histogram totals digit)) ,
  (intArray.full ( &( "count" ) ) 10 totals)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "digit" ) )) # Int |-> (digit))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (((Znth digit totals (0 : Int)) + (Znth (digit - 1) totals (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth digit totals (0 : Int)) + (Znth (digit - 1) totals (0 : Int)))) ”
) \/
(
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (totals : (List Int)) (current : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (histogram : (List Int)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) < (Z.quot max_value exponent))) (PreH10 : (1 <= digit)) (PreH11 : (digit <= 10)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH13 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) histogram)) (PreH15 : (Forall ((GE.ge (α := Int)) (n_pre)) histogram)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) totals)) (PreH17 : (Forall ((GE.ge (α := Int)) (n_pre)) totals)) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current exponent)) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH22 : (DigitPrefixTotals histogram totals digit)) ,
  (intArray.full ( &( "count" ) ) 10 totals)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "digit" ) )) # Int |-> (digit))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (((Znth digit totals (0 : Int)) + (Znth (digit - 1) totals (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth digit totals (0 : Int)) + (Znth (digit - 1) totals (0 : Int)))) ”
)

noncomputable def sort_safety_wit_21_split_goal_1 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (totals : (List Int)) (current : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (histogram : (List Int)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) < (Z.quot max_value exponent))) (PreH10 : (1 <= digit)) (PreH11 : (digit <= 10)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH13 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) histogram)) (PreH15 : (Forall ((GE.ge (α := Int)) (n_pre)) histogram)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) totals)) (PreH17 : (Forall ((GE.ge (α := Int)) (n_pre)) totals)) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current exponent)) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH22 : (DigitPrefixTotals histogram totals digit)) ,
  (intArray.full ( &( "count" ) ) 10 totals)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "digit" ) )) # Int |-> (digit))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (((Znth digit totals (0 : Int)) + (Znth (digit - 1) totals (0 : Int))) <= INT_MAX) ”

noncomputable def sort_safety_wit_21_split_goal_2 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (totals : (List Int)) (current : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (histogram : (List Int)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) < (Z.quot max_value exponent))) (PreH10 : (1 <= digit)) (PreH11 : (digit <= 10)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH13 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) histogram)) (PreH15 : (Forall ((GE.ge (α := Int)) (n_pre)) histogram)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) totals)) (PreH17 : (Forall ((GE.ge (α := Int)) (n_pre)) totals)) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current exponent)) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH22 : (DigitPrefixTotals histogram totals digit)) ,
  (intArray.full ( &( "count" ) ) 10 totals)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "digit" ) )) # Int |-> (digit))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ ((INT_MIN) <= ((Znth digit totals (0 : Int)) + (Znth (digit - 1) totals (0 : Int)))) ”

noncomputable def sort_safety_wit_22 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (totals : (List Int)) (current : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (histogram : (List Int)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) < (Z.quot max_value exponent))) (PreH10 : (1 <= digit)) (PreH11 : (digit <= 10)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH13 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) histogram)) (PreH15 : (Forall ((GE.ge (α := Int)) (n_pre)) histogram)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) totals)) (PreH17 : (Forall ((GE.ge (α := Int)) (n_pre)) totals)) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current exponent)) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH22 : (DigitPrefixTotals histogram totals digit)) ,
  (intArray.full ( &( "count" ) ) 10 totals)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "digit" ) )) # Int |-> (digit))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ ((digit - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (digit - 1)) ”

noncomputable def sort_safety_wit_23 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (totals : (List Int)) (current : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (histogram : (List Int)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) < (Z.quot max_value exponent))) (PreH10 : (1 <= digit)) (PreH11 : (digit <= 10)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH13 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) histogram)) (PreH15 : (Forall ((GE.ge (α := Int)) (n_pre)) histogram)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) totals)) (PreH17 : (Forall ((GE.ge (α := Int)) (n_pre)) totals)) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current exponent)) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH22 : (DigitPrefixTotals histogram totals digit)) ,
  (intArray.full ( &( "count" ) ) 10 totals)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "digit" ) )) # Int |-> (digit))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def sort_safety_wit_24 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (totals : (List Int)) (current : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (histogram : (List Int)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) < (Z.quot max_value exponent))) (PreH10 : (1 <= digit)) (PreH11 : (digit <= 10)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH13 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) histogram)) (PreH15 : (Forall ((GE.ge (α := Int)) (n_pre)) histogram)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) totals)) (PreH17 : (Forall ((GE.ge (α := Int)) (n_pre)) totals)) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current exponent)) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH22 : (DigitPrefixTotals histogram totals digit)) ,
  (intArray.full ( &( "count" ) ) 10 (replace_Znth (digit) (((Znth digit totals (0 : Int)) + (Znth (digit - 1) totals (0 : Int)))) (totals)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "digit" ) )) # Int |-> (digit))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ ((digit + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (digit + 1)) ”

noncomputable def sort_safety_wit_25 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (totals : (List Int)) (current : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (histogram : (List Int)) (PreH1 : (digit >= 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) < (Z.quot max_value exponent))) (PreH10 : (1 <= digit)) (PreH11 : (digit <= 10)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH13 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) histogram)) (PreH15 : (Forall ((GE.ge (α := Int)) (n_pre)) histogram)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) totals)) (PreH17 : (Forall ((GE.ge (α := Int)) (n_pre)) totals)) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current exponent)) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH22 : (DigitPrefixTotals histogram totals digit)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 totals)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ ((n_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre - 1)) ”

noncomputable def sort_safety_wit_26 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (totals : (List Int)) (current : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (histogram : (List Int)) (PreH1 : (digit >= 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) < (Z.quot max_value exponent))) (PreH10 : (1 <= digit)) (PreH11 : (digit <= 10)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH13 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) histogram)) (PreH15 : (Forall ((GE.ge (α := Int)) (n_pre)) histogram)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) totals)) (PreH17 : (Forall ((GE.ge (α := Int)) (n_pre)) totals)) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current exponent)) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH22 : (DigitPrefixTotals histogram totals digit)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 totals)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def sort_safety_wit_27 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (mixed_output : (List (Option Int))) (counters : (List Int)) (current : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (histogram : (List Int)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (histogram)) = 10)) (PreH4 : ((0 : Int) <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : ((0 : Int) < (Z.quot max_value exponent))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) histogram)) (PreH14 : (Forall ((GE.ge (α := Int)) (n_pre)) histogram)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) counters)) (PreH16 : (Forall ((GE.ge (α := Int)) (n_pre)) counters)) (PreH17 : (PrefixMaximum input n_pre max_value)) (PreH18 : (DecimalExponent exponent)) (PreH19 : (RadixPassState input current exponent)) (PreH20 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH21 : (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 counters)
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def sort_safety_wit_28 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (mixed_output : (List (Option Int))) (counters : (List Int)) (current : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (histogram : (List Int)) (PreH1 : (i >= (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) < (Z.quot max_value exponent))) (PreH10 : ((-1) <= i)) (PreH11 : (i < n_pre)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH13 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) histogram)) (PreH15 : (Forall ((GE.ge (α := Int)) (n_pre)) histogram)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) counters)) (PreH17 : (Forall ((GE.ge (α := Int)) (n_pre)) counters)) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current exponent)) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH22 : (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output)) ,
  (intArray.full a_pre n_pre current)
  ** ((( &( "digit" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full ( &( "count" ) ) 10 counters)
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)
|--
  “ (((Z.quot (Znth i current (0 : Int)) exponent) ≠ (INT_MIN)) ∨ (10 ≠ (-1))) ” &&
  “ (10 ≠ (0 : Int)) ”

noncomputable def sort_safety_wit_29 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (mixed_output : (List (Option Int))) (counters : (List Int)) (current : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (histogram : (List Int)) (PreH1 : (i >= (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) < (Z.quot max_value exponent))) (PreH10 : ((-1) <= i)) (PreH11 : (i < n_pre)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH13 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) histogram)) (PreH15 : (Forall ((GE.ge (α := Int)) (n_pre)) histogram)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) counters)) (PreH17 : (Forall ((GE.ge (α := Int)) (n_pre)) counters)) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current exponent)) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH22 : (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output)) ,
  (intArray.full a_pre n_pre current)
  ** ((( &( "digit" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full ( &( "count" ) ) 10 counters)
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)
|--
  “ (((Znth i current (0 : Int)) ≠ (INT_MIN)) ∨ (exponent ≠ (-1))) ” &&
  “ (exponent ≠ (0 : Int)) ”

noncomputable def sort_safety_wit_30 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (mixed_output : (List (Option Int))) (counters : (List Int)) (current : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (histogram : (List Int)) (PreH1 : (i >= (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) < (Z.quot max_value exponent))) (PreH10 : ((-1) <= i)) (PreH11 : (i < n_pre)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH13 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) histogram)) (PreH15 : (Forall ((GE.ge (α := Int)) (n_pre)) histogram)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) counters)) (PreH17 : (Forall ((GE.ge (α := Int)) (n_pre)) counters)) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current exponent)) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH22 : (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output)) ,
  (intArray.full a_pre n_pre current)
  ** ((( &( "digit" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full ( &( "count" ) ) 10 counters)
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)
|--
  “ (10 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 10) ”

noncomputable def sort_safety_wit_31 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (current : (List Int)) (histogram : (List Int)) (counters : (List Int)) (mixed_output : (List (Option Int))) (max_value : Int) (exponent : Int) (i : Int) (digit : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (histogram)) = 10)) (PreH4 : ((0 : Int) <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : ((0 : Int) < (Z.quot max_value exponent))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) histogram)) (PreH14 : (Forall ((GE.ge (α := Int)) (n_pre)) histogram)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) counters)) (PreH16 : (Forall ((GE.ge (α := Int)) (n_pre)) counters)) (PreH17 : (PrefixMaximum input n_pre max_value)) (PreH18 : (DecimalExponent exponent)) (PreH19 : (RadixPassState input current exponent)) (PreH20 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH21 : (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output)) (PreH22 : (digit = (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10))) (PreH23 : ((0 : Int) <= digit)) (PreH24 : (digit < 10)) (PreH25 : (1 <= (Znth (digit) (counters) ((0 : Int))))) (PreH26 : ((Znth (digit) (counters) ((0 : Int))) <= n_pre)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "digit" ) )) # Int |-> (digit))
  ** (intArray.full a_pre n_pre current)
  ** (((( &( "count" ) ) + (digit * sizeof(INT)))) # Int |-> ((Znth (digit) (counters) ((0 : Int)))))
  ** (intArray.missing_i ( &( "count" ) ) digit (0 : Int) 10 counters)
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)
|--
  “ (((Znth (digit) (counters) ((0 : Int))) - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth (digit) (counters) ((0 : Int))) - 1)) ”

noncomputable def sort_safety_wit_32 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (current : (List Int)) (histogram : (List Int)) (counters : (List Int)) (mixed_output : (List (Option Int))) (max_value : Int) (exponent : Int) (i : Int) (digit : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (histogram)) = 10)) (PreH4 : ((0 : Int) <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : ((0 : Int) < (Z.quot max_value exponent))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) histogram)) (PreH14 : (Forall ((GE.ge (α := Int)) (n_pre)) histogram)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) counters)) (PreH16 : (Forall ((GE.ge (α := Int)) (n_pre)) counters)) (PreH17 : (PrefixMaximum input n_pre max_value)) (PreH18 : (DecimalExponent exponent)) (PreH19 : (RadixPassState input current exponent)) (PreH20 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH21 : (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output)) (PreH22 : (digit = (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10))) (PreH23 : ((0 : Int) <= digit)) (PreH24 : (digit < 10)) (PreH25 : (1 <= (Znth (digit) (counters) ((0 : Int))))) (PreH26 : ((Znth (digit) (counters) ((0 : Int))) <= n_pre)) ,
  (intArray.mixed_full ( &( "output" ) ) 1000 (replace_Znth (((Znth (digit) (counters) ((0 : Int))) - 1)) ((Some ((Znth i current (0 : Int))))) (mixed_output)))
  ** (intArray.full ( &( "count" ) ) 10 (replace_Znth (digit) (((Znth (digit) (counters) ((0 : Int))) - 1)) (counters)))
  ** (intArray.full a_pre n_pre current)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "i" ) )) # Int |-> (i))
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def sort_safety_wit_33 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (mixed_output : (List (Option Int))) (counters : (List Int)) (current : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (histogram : (List Int)) (PreH1 : (i < (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) < (Z.quot max_value exponent))) (PreH10 : ((-1) <= i)) (PreH11 : (i < n_pre)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH13 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) histogram)) (PreH15 : (Forall ((GE.ge (α := Int)) (n_pre)) histogram)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) counters)) (PreH17 : (Forall ((GE.ge (α := Int)) (n_pre)) counters)) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current exponent)) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH22 : (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 counters)
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def sort_safety_wit_34 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (bucket_starts : (List Int)) (working : (List Int)) (pass_output : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (current : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (current)) = n_pre)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) pass_output)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) pass_output)) (PreH13 : (PrefixMaximum input n_pre max_value)) (PreH14 : (DecimalExponent exponent)) (PreH15 : (RadixPassState input current exponent)) (PreH16 : (StableDigitPass current pass_output exponent)) (PreH17 : (RadixCopyPrefix current pass_output working i)) ,
  (intArray.full a_pre n_pre (replace_Znth (i) ((Znth (i - (0 : Int)) pass_output (0 : Int))) (working)))
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre pass_output)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full ( &( "count" ) ) 10 bucket_starts)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 1000)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def sort_safety_wit_35 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (bucket_starts : (List Int)) (working : (List Int)) (pass_output : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (current : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (current)) = n_pre)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) pass_output)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) pass_output)) (PreH13 : (PrefixMaximum input n_pre max_value)) (PreH14 : (DecimalExponent exponent)) (PreH15 : (RadixPassState input current exponent)) (PreH16 : (StableDigitPass current pass_output exponent)) (PreH17 : (RadixCopyPrefix current pass_output working i)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** (intArray.full a_pre n_pre working)
  ** (intArray.full ( &( "count" ) ) 10 bucket_starts)
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre pass_output)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 1000)
|--
  “ ((exponent * 10) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (exponent * 10)) ”

noncomputable def sort_safety_wit_36 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (bucket_starts : (List Int)) (working : (List Int)) (pass_output : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (current : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (current)) = n_pre)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) pass_output)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) pass_output)) (PreH13 : (PrefixMaximum input n_pre max_value)) (PreH14 : (DecimalExponent exponent)) (PreH15 : (RadixPassState input current exponent)) (PreH16 : (StableDigitPass current pass_output exponent)) (PreH17 : (RadixCopyPrefix current pass_output working i)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "max_value" ) )) # Int |-> (max_value))
  ** ((( &( "exponent" ) )) # Int |-> (exponent))
  ** (intArray.full a_pre n_pre working)
  ** (intArray.full ( &( "count" ) ) 10 bucket_starts)
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre pass_output)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 1000)
|--
  “ (10 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 10) ”

noncomputable def sort_entail_wit_1 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (PreH1 : (n_pre > 1)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH5 : (Forall ((GE.ge (α := Int)) (999999999)) input)) ,
  (intArray.full a_pre n_pre input)
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= n_pre) ” &&
  “ ((0 : Int) <= (Znth (0 : Int) input (0 : Int))) ” &&
  “ ((Znth (0 : Int) input (0 : Int)) <= 999999999) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) input) ” &&
  “ (Forall ((GE.ge (α := Int)) (999999999)) input) ” &&
  “ (PrefixMaximum input 1 (Znth (0 : Int) input (0 : Int))) ”
  &&  (intArray.full a_pre n_pre input)
) \/
(
forall (n_pre : Int) (input : (List Int)) (PreH1 : (n_pre > 1)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH5 : (Forall ((GE.ge (α := Int)) (999999999)) input)) ,
  TT && emp 
|--
  “ (PrefixMaximum input 1 (Znth (0 : Int) input (0 : Int))) ” &&
  “ ((Znth (0 : Int) input (0 : Int)) <= 999999999) ” &&
  “ ((0 : Int) <= (Znth (0 : Int) input (0 : Int))) ”
  &&  emp
)

noncomputable def sort_entail_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (PreH1 : (n_pre > 1)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH5 : (Forall ((GE.ge (α := Int)) (999999999)) input)) ,
  (PrefixMaximum input 1 (Znth (0 : Int) input (0 : Int)))

noncomputable def sort_entail_wit_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (PreH1 : (n_pre > 1)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH5 : (Forall ((GE.ge (α := Int)) (999999999)) input)) ,
  ((Znth (0 : Int) input (0 : Int)) <= 999999999)

noncomputable def sort_entail_wit_1_split_goal_3 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (PreH1 : (n_pre > 1)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH5 : (Forall ((GE.ge (α := Int)) (999999999)) input)) ,
  ((0 : Int) <= (Znth (0 : Int) input (0 : Int)))

noncomputable def sort_entail_wit_2_1 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (max_value : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) > max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GE.ge (α := Int)) (999999999)) input)) (PreH11 : (PrefixMaximum input i max_value)) ,
  (intArray.full a_pre n_pre input)
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= (Znth i input (0 : Int))) ” &&
  “ ((Znth i input (0 : Int)) <= 999999999) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) input) ” &&
  “ (Forall ((GE.ge (α := Int)) (999999999)) input) ” &&
  “ (PrefixMaximum input (i + 1) (Znth i input (0 : Int))) ”
  &&  (intArray.full a_pre n_pre input)
) \/
(
forall (n_pre : Int) (input : (List Int)) (max_value : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) > max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GE.ge (α := Int)) (999999999)) input)) (PreH11 : (PrefixMaximum input i max_value)) ,
  TT && emp 
|--
  “ (PrefixMaximum input (i + 1) (Znth i input (0 : Int))) ” &&
  “ ((Znth i input (0 : Int)) <= 999999999) ”
  &&  emp
)

noncomputable def sort_entail_wit_2_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (max_value : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) > max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GE.ge (α := Int)) (999999999)) input)) (PreH11 : (PrefixMaximum input i max_value)) ,
  (PrefixMaximum input (i + 1) (Znth i input (0 : Int)))

noncomputable def sort_entail_wit_2_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (max_value : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) > max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GE.ge (α := Int)) (999999999)) input)) (PreH11 : (PrefixMaximum input i max_value)) ,
  ((Znth i input (0 : Int)) <= 999999999)

noncomputable def sort_entail_wit_2_2 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (max_value : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) <= max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GE.ge (α := Int)) (999999999)) input)) (PreH11 : (PrefixMaximum input i max_value)) ,
  (intArray.full a_pre n_pre input)
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) input) ” &&
  “ (Forall ((GE.ge (α := Int)) (999999999)) input) ” &&
  “ (PrefixMaximum input (i + 1) max_value) ”
  &&  (intArray.full a_pre n_pre input)
) \/
(
forall (n_pre : Int) (input : (List Int)) (max_value : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) <= max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GE.ge (α := Int)) (999999999)) input)) (PreH11 : (PrefixMaximum input i max_value)) ,
  TT && emp 
|--
  “ (PrefixMaximum input (i + 1) max_value) ”
  &&  emp
)

noncomputable def sort_entail_wit_2_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (max_value : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) <= max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GE.ge (α := Int)) (999999999)) input)) (PreH11 : (PrefixMaximum input i max_value)) ,
  (PrefixMaximum input (i + 1) max_value)

noncomputable def sort_entail_wit_3 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (max_value : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((0 : Int) <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH9 : (Forall ((GE.ge (α := Int)) (999999999)) input)) (PreH10 : (PrefixMaximum input i max_value)) ,
  (intArray.undef_full ( &( "count" ) ) 10)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
  ** (intArray.full a_pre n_pre input)
|--
  EX current : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= 1000000000) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) current) ” &&
  “ (Forall ((GE.ge (α := Int)) (999999999)) current) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent 1) ” &&
  “ (RadixPassState input current 1) ”
  &&  (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
  ** (intArray.undef_full ( &( "count" ) ) 10)
) \/
(
forall (n_pre : Int) (input : (List Int)) (max_value : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((0 : Int) <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH9 : (Forall ((GE.ge (α := Int)) (999999999)) input)) (PreH10 : (PrefixMaximum input i max_value)) ,
  TT && emp 
|--
  “ (RadixPassState input input 1) ” &&
  “ (DecimalExponent 1) ” &&
  “ (PrefixMaximum input n_pre max_value) ”
  &&  emp
)

noncomputable def sort_entail_wit_3_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (max_value : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((0 : Int) <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH9 : (Forall ((GE.ge (α := Int)) (999999999)) input)) (PreH10 : (PrefixMaximum input i max_value)) ,
  (RadixPassState input input 1)

noncomputable def sort_entail_wit_3_split_goal_2 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (max_value : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((0 : Int) <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH9 : (Forall ((GE.ge (α := Int)) (999999999)) input)) (PreH10 : (PrefixMaximum input i max_value)) ,
  (DecimalExponent 1)

noncomputable def sort_entail_wit_3_split_goal_3 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (max_value : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((0 : Int) <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH9 : (Forall ((GE.ge (α := Int)) (999999999)) input)) (PreH10 : (PrefixMaximum input i max_value)) ,
  (PrefixMaximum input n_pre max_value)

noncomputable def sort_entail_wit_4 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (current_2 : (List Int)) (exponent : Int) (max_value : Int) (PreH1 : ((Z.quot max_value exponent) > (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 1000000000)) (PreH8 : (Forall ((LE.le (α := Int)) ((0 : Int))) current_2)) (PreH9 : (Forall ((GE.ge (α := Int)) (999999999)) current_2)) (PreH10 : (PrefixMaximum input n_pre max_value)) (PreH11 : (DecimalExponent exponent)) (PreH12 : (RadixPassState input current_2 exponent)) ,
  (intArray.full a_pre n_pre current_2)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
  ** (intArray.undef_full ( &( "count" ) ) 10)
|--
  EX zero_prefix : (List Int), EX current : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 10) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) current) ” &&
  “ (Forall ((GE.ge (α := Int)) (999999999)) current) ” &&
  “ (Forall (Eq ((0 : Int))) zero_prefix) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ”
  &&  (intArray.full a_pre n_pre current)
  ** (intArray.seg ( &( "count" ) ) (0 : Int) (0 : Int) zero_prefix)
  ** (intArray.undef_seg ( &( "count" ) ) (0 : Int) 10)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
) \/
(
forall (n_pre : Int) (input : (List Int)) (current_2 : (List Int)) (exponent : Int) (max_value : Int) (PreH1 : ((Z.quot max_value exponent) > (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 1000000000)) (PreH8 : (Forall ((LE.le (α := Int)) ((0 : Int))) current_2)) (PreH9 : (Forall ((GE.ge (α := Int)) (999999999)) current_2)) (PreH10 : (PrefixMaximum input n_pre max_value)) (PreH11 : (DecimalExponent exponent)) (PreH12 : (RadixPassState input current_2 exponent)) ,
  TT && emp 
|--
  “ (Forall (Eq ((0 : Int))) (@List.nil Int)) ” &&
  “ (exponent <= 100000000) ”
  &&  emp
)

noncomputable def sort_entail_wit_4_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (current_2 : (List Int)) (exponent : Int) (max_value : Int) (PreH1 : ((Z.quot max_value exponent) > (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 1000000000)) (PreH8 : (Forall ((LE.le (α := Int)) ((0 : Int))) current_2)) (PreH9 : (Forall ((GE.ge (α := Int)) (999999999)) current_2)) (PreH10 : (PrefixMaximum input n_pre max_value)) (PreH11 : (DecimalExponent exponent)) (PreH12 : (RadixPassState input current_2 exponent)) ,
  (Forall (Eq ((0 : Int))) (@List.nil Int))

noncomputable def sort_entail_wit_4_split_goal_2 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (current_2 : (List Int)) (exponent : Int) (max_value : Int) (PreH1 : ((Z.quot max_value exponent) > (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 1000000000)) (PreH8 : (Forall ((LE.le (α := Int)) ((0 : Int))) current_2)) (PreH9 : (Forall ((GE.ge (α := Int)) (999999999)) current_2)) (PreH10 : (PrefixMaximum input n_pre max_value)) (PreH11 : (DecimalExponent exponent)) (PreH12 : (RadixPassState input current_2 exponent)) ,
  (exponent <= 100000000)

noncomputable def sort_entail_wit_5 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (zero_prefix_2 : (List Int)) (current_2 : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : ((0 : Int) < (Z.quot max_value exponent))) (PreH9 : ((0 : Int) <= digit)) (PreH10 : (digit <= 10)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) current_2)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) current_2)) (PreH13 : (Forall (Eq ((0 : Int))) zero_prefix_2)) (PreH14 : (PrefixMaximum input n_pre max_value)) (PreH15 : (DecimalExponent exponent)) (PreH16 : (RadixPassState input current_2 exponent)) ,
  (intArray.seg ( &( "count" ) ) (0 : Int) (digit + 1) (zero_prefix_2 ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "count" ) ) (digit + 1) 10)
  ** (intArray.full a_pre n_pre current_2)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  EX zero_prefix : (List Int), EX current : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((0 : Int) <= (digit + 1)) ” &&
  “ ((digit + 1) <= 10) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) current) ” &&
  “ (Forall ((GE.ge (α := Int)) (999999999)) current) ” &&
  “ (Forall (Eq ((0 : Int))) zero_prefix) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ”
  &&  (intArray.full a_pre n_pre current)
  ** (intArray.seg ( &( "count" ) ) (0 : Int) (digit + 1) zero_prefix)
  ** (intArray.undef_seg ( &( "count" ) ) (digit + 1) 10)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
) \/
(
forall (n_pre : Int) (input : (List Int)) (zero_prefix_2 : (List Int)) (current_2 : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : ((0 : Int) < (Z.quot max_value exponent))) (PreH9 : ((0 : Int) <= digit)) (PreH10 : (digit <= 10)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) current_2)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) current_2)) (PreH13 : (Forall (Eq ((0 : Int))) zero_prefix_2)) (PreH14 : (PrefixMaximum input n_pre max_value)) (PreH15 : (DecimalExponent exponent)) (PreH16 : (RadixPassState input current_2 exponent)) ,
  TT && emp 
|--
  “ (Forall (Eq ((0 : Int))) (zero_prefix_2 ++ ((0 : Int) :: (@List.nil Int)))) ”
  &&  emp
)

noncomputable def sort_entail_wit_5_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (zero_prefix_2 : (List Int)) (current_2 : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : ((0 : Int) < (Z.quot max_value exponent))) (PreH9 : ((0 : Int) <= digit)) (PreH10 : (digit <= 10)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) current_2)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) current_2)) (PreH13 : (Forall (Eq ((0 : Int))) zero_prefix_2)) (PreH14 : (PrefixMaximum input n_pre max_value)) (PreH15 : (DecimalExponent exponent)) (PreH16 : (RadixPassState input current_2 exponent)) ,
  (Forall (Eq ((0 : Int))) (zero_prefix_2 ++ ((0 : Int) :: (@List.nil Int))))

noncomputable def sort_entail_wit_6 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (zero_prefix : (List Int)) (current_2 : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (PreH1 : (digit >= 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : ((0 : Int) < (Z.quot max_value exponent))) (PreH9 : ((0 : Int) <= digit)) (PreH10 : (digit <= 10)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) current_2)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) current_2)) (PreH13 : (Forall (Eq ((0 : Int))) zero_prefix)) (PreH14 : (PrefixMaximum input n_pre max_value)) (PreH15 : (DecimalExponent exponent)) (PreH16 : (RadixPassState input current_2 exponent)) ,
  (intArray.full a_pre n_pre current_2)
  ** (intArray.seg ( &( "count" ) ) (0 : Int) digit zero_prefix)
  ** (intArray.undef_seg ( &( "count" ) ) digit 10)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  EX counts : (List Int), EX current : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) current) ” &&
  “ (Forall ((GE.ge (α := Int)) (999999999)) current) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts) ” &&
  “ (Forall ((GE.ge (α := Int)) ((0 : Int))) counts) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent (0 : Int) counts) ”
  &&  (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 counts)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
) \/
(
forall (n_pre : Int) (input : (List Int)) (zero_prefix : (List Int)) (current_2 : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (PreH1 : (digit >= 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : ((0 : Int) < (Z.quot max_value exponent))) (PreH9 : ((0 : Int) <= digit)) (PreH10 : (digit <= 10)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) current_2)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) current_2)) (PreH13 : (Forall (Eq ((0 : Int))) zero_prefix)) (PreH14 : (PrefixMaximum input n_pre max_value)) (PreH15 : (DecimalExponent exponent)) (PreH16 : (RadixPassState input current_2 exponent)) ,
  (intArray.seg ( &( "count" ) ) (0 : Int) digit zero_prefix)
|--
  EX counts : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) current_2) ” &&
  “ (Forall ((GE.ge (α := Int)) (999999999)) current_2) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts) ” &&
  “ (Forall ((GE.ge (α := Int)) ((0 : Int))) counts) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current_2 exponent) ” &&
  “ (DigitHistogramPrefix current_2 exponent (0 : Int) counts) ”
  &&  (intArray.full ( &( "count" ) ) 10 counts)
)

noncomputable def sort_entail_wit_7 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (counts_2 : (List Int)) (current : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : ((0 : Int) < (Z.quot max_value exponent))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (i)) counts_2)) (PreH15 : (PrefixMaximum input n_pre max_value)) (PreH16 : (DecimalExponent exponent)) (PreH17 : (RadixPassState input current exponent)) (PreH18 : (DigitHistogramPrefix current exponent i counts_2)) ,
  (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 counts_2)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  EX counts : (List Int), EX current_2 : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) current_2) ” &&
  “ (Forall ((GE.ge (α := Int)) (999999999)) current_2) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts) ” &&
  “ (Forall ((GE.ge (α := Int)) (i)) counts) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current_2 exponent) ” &&
  “ (DigitHistogramPrefix current_2 exponent i counts) ” &&
  “ ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) = (Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10)) ” &&
  “ ((0 : Int) <= (Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10)) ” &&
  “ ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) < 10) ”
  &&  (intArray.full a_pre n_pre current_2)
  ** (intArray.full ( &( "count" ) ) 10 counts)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
) \/
(
forall (n_pre : Int) (input : (List Int)) (counts_2 : (List Int)) (current : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : ((0 : Int) < (Z.quot max_value exponent))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (i)) counts_2)) (PreH15 : (PrefixMaximum input n_pre max_value)) (PreH16 : (DecimalExponent exponent)) (PreH17 : (RadixPassState input current exponent)) (PreH18 : (DigitHistogramPrefix current exponent i counts_2)) ,
  TT && emp 
|--
  “ ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) < 10) ” &&
  “ ((0 : Int) <= (Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10)) ”
  &&  emp
)

noncomputable def sort_entail_wit_7_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (counts_2 : (List Int)) (current : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : ((0 : Int) < (Z.quot max_value exponent))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (i)) counts_2)) (PreH15 : (PrefixMaximum input n_pre max_value)) (PreH16 : (DecimalExponent exponent)) (PreH17 : (RadixPassState input current exponent)) (PreH18 : (DigitHistogramPrefix current exponent i counts_2)) ,
  ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) < 10)

noncomputable def sort_entail_wit_7_split_goal_2 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (counts_2 : (List Int)) (current : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : ((0 : Int) < (Z.quot max_value exponent))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (i)) counts_2)) (PreH15 : (PrefixMaximum input n_pre max_value)) (PreH16 : (DecimalExponent exponent)) (PreH17 : (RadixPassState input current exponent)) (PreH18 : (DigitHistogramPrefix current exponent i counts_2)) ,
  ((0 : Int) <= (Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10))

noncomputable def sort_entail_wit_8 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (current_2 : (List Int)) (counts_2 : (List Int)) (max_value : Int) (exponent : Int) (i : Int) (digit : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= max_value)) (PreH4 : (max_value <= 999999999)) (PreH5 : (1 <= exponent)) (PreH6 : (exponent <= 100000000)) (PreH7 : ((0 : Int) < (Z.quot max_value exponent))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) current_2)) (PreH11 : (Forall ((GE.ge (α := Int)) (999999999)) current_2)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_2)) (PreH13 : (Forall ((GE.ge (α := Int)) (i)) counts_2)) (PreH14 : (PrefixMaximum input n_pre max_value)) (PreH15 : (DecimalExponent exponent)) (PreH16 : (RadixPassState input current_2 exponent)) (PreH17 : (DigitHistogramPrefix current_2 exponent i counts_2)) (PreH18 : (digit = (Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10))) (PreH19 : ((0 : Int) <= digit)) (PreH20 : (digit < 10)) ,
  (intArray.full ( &( "count" ) ) 10 (replace_Znth (digit) (((Znth digit counts_2 (0 : Int)) + 1)) (counts_2)))
  ** (intArray.full a_pre n_pre current_2)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  EX counts : (List Int), EX current : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) current) ” &&
  “ (Forall ((GE.ge (α := Int)) (999999999)) current) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts) ” &&
  “ (Forall ((GE.ge (α := Int)) ((i + 1))) counts) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent (i + 1) counts) ”
  &&  (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 counts)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
) \/
(
forall (n_pre : Int) (input : (List Int)) (current_2 : (List Int)) (counts_2 : (List Int)) (max_value : Int) (exponent : Int) (i : Int) (digit : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= max_value)) (PreH4 : (max_value <= 999999999)) (PreH5 : (1 <= exponent)) (PreH6 : (exponent <= 100000000)) (PreH7 : ((0 : Int) < (Z.quot max_value exponent))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) current_2)) (PreH11 : (Forall ((GE.ge (α := Int)) (999999999)) current_2)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_2)) (PreH13 : (Forall ((GE.ge (α := Int)) (i)) counts_2)) (PreH14 : (PrefixMaximum input n_pre max_value)) (PreH15 : (DecimalExponent exponent)) (PreH16 : (RadixPassState input current_2 exponent)) (PreH17 : (DigitHistogramPrefix current_2 exponent i counts_2)) (PreH18 : (digit = (Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10))) (PreH19 : ((0 : Int) <= digit)) (PreH20 : (digit < 10)) ,
  TT && emp 
|--
  “ (DigitHistogramPrefix current_2 exponent (i + 1) (replace_Znth (digit) (((Znth digit counts_2 (0 : Int)) + 1)) (counts_2))) ” &&
  “ (Forall ((GE.ge (α := Int)) ((i + 1))) (replace_Znth (digit) (((Znth digit counts_2 (0 : Int)) + 1)) (counts_2))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (replace_Znth (digit) (((Znth digit counts_2 (0 : Int)) + 1)) (counts_2))) ”
  &&  emp
)

noncomputable def sort_entail_wit_8_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (current_2 : (List Int)) (counts_2 : (List Int)) (max_value : Int) (exponent : Int) (i : Int) (digit : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= max_value)) (PreH4 : (max_value <= 999999999)) (PreH5 : (1 <= exponent)) (PreH6 : (exponent <= 100000000)) (PreH7 : ((0 : Int) < (Z.quot max_value exponent))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) current_2)) (PreH11 : (Forall ((GE.ge (α := Int)) (999999999)) current_2)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_2)) (PreH13 : (Forall ((GE.ge (α := Int)) (i)) counts_2)) (PreH14 : (PrefixMaximum input n_pre max_value)) (PreH15 : (DecimalExponent exponent)) (PreH16 : (RadixPassState input current_2 exponent)) (PreH17 : (DigitHistogramPrefix current_2 exponent i counts_2)) (PreH18 : (digit = (Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10))) (PreH19 : ((0 : Int) <= digit)) (PreH20 : (digit < 10)) ,
  (DigitHistogramPrefix current_2 exponent (i + 1) (replace_Znth (digit) (((Znth digit counts_2 (0 : Int)) + 1)) (counts_2)))

noncomputable def sort_entail_wit_8_split_goal_2 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (current_2 : (List Int)) (counts_2 : (List Int)) (max_value : Int) (exponent : Int) (i : Int) (digit : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= max_value)) (PreH4 : (max_value <= 999999999)) (PreH5 : (1 <= exponent)) (PreH6 : (exponent <= 100000000)) (PreH7 : ((0 : Int) < (Z.quot max_value exponent))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) current_2)) (PreH11 : (Forall ((GE.ge (α := Int)) (999999999)) current_2)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_2)) (PreH13 : (Forall ((GE.ge (α := Int)) (i)) counts_2)) (PreH14 : (PrefixMaximum input n_pre max_value)) (PreH15 : (DecimalExponent exponent)) (PreH16 : (RadixPassState input current_2 exponent)) (PreH17 : (DigitHistogramPrefix current_2 exponent i counts_2)) (PreH18 : (digit = (Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10))) (PreH19 : ((0 : Int) <= digit)) (PreH20 : (digit < 10)) ,
  (Forall ((GE.ge (α := Int)) ((i + 1))) (replace_Znth (digit) (((Znth digit counts_2 (0 : Int)) + 1)) (counts_2)))

noncomputable def sort_entail_wit_8_split_goal_3 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (current_2 : (List Int)) (counts_2 : (List Int)) (max_value : Int) (exponent : Int) (i : Int) (digit : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= max_value)) (PreH4 : (max_value <= 999999999)) (PreH5 : (1 <= exponent)) (PreH6 : (exponent <= 100000000)) (PreH7 : ((0 : Int) < (Z.quot max_value exponent))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) current_2)) (PreH11 : (Forall ((GE.ge (α := Int)) (999999999)) current_2)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_2)) (PreH13 : (Forall ((GE.ge (α := Int)) (i)) counts_2)) (PreH14 : (PrefixMaximum input n_pre max_value)) (PreH15 : (DecimalExponent exponent)) (PreH16 : (RadixPassState input current_2 exponent)) (PreH17 : (DigitHistogramPrefix current_2 exponent i counts_2)) (PreH18 : (digit = (Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10))) (PreH19 : ((0 : Int) <= digit)) (PreH20 : (digit < 10)) ,
  (Forall ((LE.le (α := Int)) ((0 : Int))) (replace_Znth (digit) (((Znth digit counts_2 (0 : Int)) + 1)) (counts_2)))

noncomputable def sort_entail_wit_9 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (counts : (List Int)) (current_2 : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : ((0 : Int) < (Z.quot max_value exponent))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) current_2)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) current_2)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts)) (PreH14 : (Forall ((GE.ge (α := Int)) (i)) counts)) (PreH15 : (PrefixMaximum input n_pre max_value)) (PreH16 : (DecimalExponent exponent)) (PreH17 : (RadixPassState input current_2 exponent)) (PreH18 : (DigitHistogramPrefix current_2 exponent i counts)) ,
  (intArray.full a_pre n_pre current_2)
  ** (intArray.full ( &( "count" ) ) 10 counts)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  EX totals : (List Int), EX current : (List Int), EX histogram : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (histogram)) = 10) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= 10) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) current) ” &&
  “ (Forall ((GE.ge (α := Int)) (999999999)) current) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) histogram) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) histogram) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) totals) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) totals) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent n_pre histogram) ” &&
  “ (DigitPrefixTotals histogram totals 1) ”
  &&  (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 totals)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
) \/
(
forall (n_pre : Int) (input : (List Int)) (counts : (List Int)) (current_2 : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : ((0 : Int) < (Z.quot max_value exponent))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) current_2)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) current_2)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts)) (PreH14 : (Forall ((GE.ge (α := Int)) (i)) counts)) (PreH15 : (PrefixMaximum input n_pre max_value)) (PreH16 : (DecimalExponent exponent)) (PreH17 : (RadixPassState input current_2 exponent)) (PreH18 : (DigitHistogramPrefix current_2 exponent i counts)) ,
  TT && emp 
|--
  EX histogram : (List Int),
  “ ((Zlength (histogram)) = 10) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= 10) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) histogram) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) histogram) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) counts) ” &&
  “ (DigitHistogramPrefix current_2 exponent n_pre histogram) ” &&
  “ (DigitPrefixTotals histogram counts 1) ”
  &&  emp
)

noncomputable def sort_entail_wit_10 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (totals_2 : (List Int)) (current_2 : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (histogram_2 : (List Int)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram_2)) = 10)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) < (Z.quot max_value exponent))) (PreH10 : (1 <= digit)) (PreH11 : (digit <= 10)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) current_2)) (PreH13 : (Forall ((GE.ge (α := Int)) (999999999)) current_2)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) histogram_2)) (PreH15 : (Forall ((GE.ge (α := Int)) (n_pre)) histogram_2)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) totals_2)) (PreH17 : (Forall ((GE.ge (α := Int)) (n_pre)) totals_2)) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current_2 exponent)) (PreH21 : (DigitHistogramPrefix current_2 exponent n_pre histogram_2)) (PreH22 : (DigitPrefixTotals histogram_2 totals_2 digit)) ,
  (intArray.full ( &( "count" ) ) 10 (replace_Znth (digit) (((Znth digit totals_2 (0 : Int)) + (Znth (digit - 1) totals_2 (0 : Int)))) (totals_2)))
  ** (intArray.full a_pre n_pre current_2)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  EX totals : (List Int), EX current : (List Int), EX histogram : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (histogram)) = 10) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ (1 <= (digit + 1)) ” &&
  “ ((digit + 1) <= 10) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) current) ” &&
  “ (Forall ((GE.ge (α := Int)) (999999999)) current) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) histogram) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) histogram) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) totals) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) totals) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent n_pre histogram) ” &&
  “ (DigitPrefixTotals histogram totals (digit + 1)) ”
  &&  (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 totals)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
) \/
(
forall (n_pre : Int) (input : (List Int)) (totals_2 : (List Int)) (current_2 : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (histogram_2 : (List Int)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram_2)) = 10)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) < (Z.quot max_value exponent))) (PreH10 : (1 <= digit)) (PreH11 : (digit <= 10)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) current_2)) (PreH13 : (Forall ((GE.ge (α := Int)) (999999999)) current_2)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) histogram_2)) (PreH15 : (Forall ((GE.ge (α := Int)) (n_pre)) histogram_2)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) totals_2)) (PreH17 : (Forall ((GE.ge (α := Int)) (n_pre)) totals_2)) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current_2 exponent)) (PreH21 : (DigitHistogramPrefix current_2 exponent n_pre histogram_2)) (PreH22 : (DigitPrefixTotals histogram_2 totals_2 digit)) ,
  TT && emp 
|--
  EX histogram : (List Int),
  “ ((Zlength (histogram)) = 10) ” &&
  “ (1 <= (digit + 1)) ” &&
  “ ((digit + 1) <= 10) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) histogram) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) histogram) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (replace_Znth (digit) (((Znth digit totals_2 (0 : Int)) + (Znth (digit - 1) totals_2 (0 : Int)))) (totals_2))) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) (replace_Znth (digit) (((Znth digit totals_2 (0 : Int)) + (Znth (digit - 1) totals_2 (0 : Int)))) (totals_2))) ” &&
  “ (DigitHistogramPrefix current_2 exponent n_pre histogram) ” &&
  “ (DigitPrefixTotals histogram (replace_Znth (digit) (((Znth digit totals_2 (0 : Int)) + (Znth (digit - 1) totals_2 (0 : Int)))) (totals_2)) (digit + 1)) ”
  &&  emp
)

noncomputable def sort_entail_wit_11 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (totals : (List Int)) (current_2 : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (histogram_2 : (List Int)) (PreH1 : (digit >= 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram_2)) = 10)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) < (Z.quot max_value exponent))) (PreH10 : (1 <= digit)) (PreH11 : (digit <= 10)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) current_2)) (PreH13 : (Forall ((GE.ge (α := Int)) (999999999)) current_2)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) histogram_2)) (PreH15 : (Forall ((GE.ge (α := Int)) (n_pre)) histogram_2)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) totals)) (PreH17 : (Forall ((GE.ge (α := Int)) (n_pre)) totals)) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current_2 exponent)) (PreH21 : (DigitHistogramPrefix current_2 exponent n_pre histogram_2)) (PreH22 : (DigitPrefixTotals histogram_2 totals digit)) ,
  (intArray.full a_pre n_pre current_2)
  ** (intArray.full ( &( "count" ) ) 10 totals)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  EX mixed_output : (List (Option Int)), EX counters : (List Int), EX current : (List Int), EX histogram : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (histogram)) = 10) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((-1) <= (n_pre - 1)) ” &&
  “ ((n_pre - 1) < n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) current) ” &&
  “ (Forall ((GE.ge (α := Int)) (999999999)) current) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) histogram) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) histogram) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counters) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) counters) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent n_pre histogram) ” &&
  “ (BucketPlacementProgress current exponent ((n_pre - 1) + 1) histogram counters mixed_output) ”
  &&  (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 counters)
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)
) \/
(
forall (n_pre : Int) (input : (List Int)) (totals : (List Int)) (current_2 : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (histogram_2 : (List Int)) (PreH1 : (digit >= 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram_2)) = 10)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) < (Z.quot max_value exponent))) (PreH10 : (1 <= digit)) (PreH11 : (digit <= 10)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) current_2)) (PreH13 : (Forall ((GE.ge (α := Int)) (999999999)) current_2)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) histogram_2)) (PreH15 : (Forall ((GE.ge (α := Int)) (n_pre)) histogram_2)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) totals)) (PreH17 : (Forall ((GE.ge (α := Int)) (n_pre)) totals)) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current_2 exponent)) (PreH21 : (DigitHistogramPrefix current_2 exponent n_pre histogram_2)) (PreH22 : (DigitPrefixTotals histogram_2 totals digit)) ,
  (intArray.undef_full ( &( "output" ) ) 1000)
|--
  EX mixed_output : (List (Option Int)), EX histogram : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (histogram)) = 10) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((-1) <= (n_pre - 1)) ” &&
  “ ((n_pre - 1) < n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) current_2) ” &&
  “ (Forall ((GE.ge (α := Int)) (999999999)) current_2) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) histogram) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) histogram) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) totals) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) totals) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current_2 exponent) ” &&
  “ (DigitHistogramPrefix current_2 exponent n_pre histogram) ” &&
  “ (BucketPlacementProgress current_2 exponent ((n_pre - 1) + 1) histogram totals mixed_output) ”
  &&  (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)
)

noncomputable def sort_entail_wit_12 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (mixed_output_2 : (List (Option Int))) (counters_2 : (List Int)) (current : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (histogram_2 : (List Int)) (PreH1 : (i >= (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram_2)) = 10)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) < (Z.quot max_value exponent))) (PreH10 : ((-1) <= i)) (PreH11 : (i < n_pre)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH13 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) histogram_2)) (PreH15 : (Forall ((GE.ge (α := Int)) (n_pre)) histogram_2)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) counters_2)) (PreH17 : (Forall ((GE.ge (α := Int)) (n_pre)) counters_2)) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current exponent)) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram_2)) (PreH22 : (BucketPlacementProgress current exponent (i + 1) histogram_2 counters_2 mixed_output_2)) ,
  (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 counters_2)
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output_2)
|--
  EX mixed_output : (List (Option Int)), EX counters : (List Int), EX current_2 : (List Int), EX histogram : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (histogram)) = 10) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) current_2) ” &&
  “ (Forall ((GE.ge (α := Int)) (999999999)) current_2) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) histogram) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) histogram) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counters) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) counters) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current_2 exponent) ” &&
  “ (DigitHistogramPrefix current_2 exponent n_pre histogram) ” &&
  “ (BucketPlacementProgress current_2 exponent (i + 1) histogram counters mixed_output) ” &&
  “ ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) = (Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10)) ” &&
  “ ((0 : Int) <= (Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10)) ” &&
  “ ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) < 10) ” &&
  “ (1 <= (Znth ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10)) (counters) ((0 : Int)))) ” &&
  “ ((Znth ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10)) (counters) ((0 : Int))) <= n_pre) ”
  &&  (intArray.full a_pre n_pre current_2)
  ** (((( &( "count" ) ) + ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) * sizeof(INT)))) # Int |-> ((Znth ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10)) (counters) ((0 : Int)))))
  ** (intArray.missing_i ( &( "count" ) ) (Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) (0 : Int) 10 counters)
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)
) \/
(
forall (n_pre : Int) (input : (List Int)) (mixed_output_2 : (List (Option Int))) (counters_2 : (List Int)) (current : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (histogram_2 : (List Int)) (PreH1 : (i >= (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram_2)) = 10)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) < (Z.quot max_value exponent))) (PreH10 : ((-1) <= i)) (PreH11 : (i < n_pre)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH13 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) histogram_2)) (PreH15 : (Forall ((GE.ge (α := Int)) (n_pre)) histogram_2)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) counters_2)) (PreH17 : (Forall ((GE.ge (α := Int)) (n_pre)) counters_2)) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current exponent)) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram_2)) (PreH22 : (BucketPlacementProgress current exponent (i + 1) histogram_2 counters_2 mixed_output_2)) ,
  (intArray.full ( &( "count" ) ) 10 counters_2)
|--
  EX counters : (List Int), EX histogram : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (histogram)) = 10) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) current) ” &&
  “ (Forall ((GE.ge (α := Int)) (999999999)) current) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) histogram) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) histogram) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counters) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) counters) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent n_pre histogram) ” &&
  “ (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output_2) ” &&
  “ ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) = (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) ” &&
  “ ((0 : Int) <= (Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10)) ” &&
  “ ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) < 10) ” &&
  “ (1 <= (Znth ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10)) (counters) ((0 : Int)))) ” &&
  “ ((Znth ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10)) (counters) ((0 : Int))) <= n_pre) ”
  &&  (((( &( "count" ) ) + ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) * sizeof(INT)))) # Int |-> ((Znth ((Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10)) (counters) ((0 : Int)))))
  ** (intArray.missing_i ( &( "count" ) ) (Z.rem (Z.quot (Znth i current (0 : Int)) exponent) 10) (0 : Int) 10 counters)
)

noncomputable def sort_entail_wit_13 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (current_2 : (List Int)) (histogram_2 : (List Int)) (counters_2 : (List Int)) (mixed_output_2 : (List (Option Int))) (max_value : Int) (exponent : Int) (i : Int) (digit : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (histogram_2)) = 10)) (PreH4 : ((0 : Int) <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : ((0 : Int) < (Z.quot max_value exponent))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) current_2)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) current_2)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) histogram_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (n_pre)) histogram_2)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) counters_2)) (PreH16 : (Forall ((GE.ge (α := Int)) (n_pre)) counters_2)) (PreH17 : (PrefixMaximum input n_pre max_value)) (PreH18 : (DecimalExponent exponent)) (PreH19 : (RadixPassState input current_2 exponent)) (PreH20 : (DigitHistogramPrefix current_2 exponent n_pre histogram_2)) (PreH21 : (BucketPlacementProgress current_2 exponent (i + 1) histogram_2 counters_2 mixed_output_2)) (PreH22 : (digit = (Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10))) (PreH23 : ((0 : Int) <= digit)) (PreH24 : (digit < 10)) (PreH25 : (1 <= (Znth (digit) (counters_2) ((0 : Int))))) (PreH26 : ((Znth (digit) (counters_2) ((0 : Int))) <= n_pre)) ,
  (intArray.mixed_full ( &( "output" ) ) 1000 (replace_Znth (((Znth (digit) (counters_2) ((0 : Int))) - 1)) ((Some ((Znth i current_2 (0 : Int))))) (mixed_output_2)))
  ** (intArray.full ( &( "count" ) ) 10 (replace_Znth (digit) (((Znth (digit) (counters_2) ((0 : Int))) - 1)) (counters_2)))
  ** (intArray.full a_pre n_pre current_2)
|--
  EX mixed_output : (List (Option Int)), EX counters : (List Int), EX current : (List Int), EX histogram : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (histogram)) = 10) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((-1) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) current) ” &&
  “ (Forall ((GE.ge (α := Int)) (999999999)) current) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) histogram) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) histogram) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counters) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) counters) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent n_pre histogram) ” &&
  “ (BucketPlacementProgress current exponent ((i - 1) + 1) histogram counters mixed_output) ”
  &&  (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 counters)
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)
) \/
(
forall (n_pre : Int) (input : (List Int)) (current_2 : (List Int)) (histogram_2 : (List Int)) (counters_2 : (List Int)) (mixed_output_2 : (List (Option Int))) (max_value : Int) (exponent : Int) (i : Int) (digit : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (histogram_2)) = 10)) (PreH4 : ((0 : Int) <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : ((0 : Int) < (Z.quot max_value exponent))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) current_2)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) current_2)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) histogram_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (n_pre)) histogram_2)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) counters_2)) (PreH16 : (Forall ((GE.ge (α := Int)) (n_pre)) counters_2)) (PreH17 : (PrefixMaximum input n_pre max_value)) (PreH18 : (DecimalExponent exponent)) (PreH19 : (RadixPassState input current_2 exponent)) (PreH20 : (DigitHistogramPrefix current_2 exponent n_pre histogram_2)) (PreH21 : (BucketPlacementProgress current_2 exponent (i + 1) histogram_2 counters_2 mixed_output_2)) (PreH22 : (digit = (Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10))) (PreH23 : ((0 : Int) <= digit)) (PreH24 : (digit < 10)) (PreH25 : (1 <= (Znth (digit) (counters_2) ((0 : Int))))) (PreH26 : ((Znth (digit) (counters_2) ((0 : Int))) <= n_pre)) ,
  TT && emp 
|--
  EX histogram : (List Int),
  “ ((Zlength (histogram)) = 10) ” &&
  “ ((-1) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) histogram) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) histogram) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (replace_Znth ((Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10)) (((Znth ((Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10)) (counters_2) ((0 : Int))) - 1)) (counters_2))) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) (replace_Znth ((Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10)) (((Znth ((Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10)) (counters_2) ((0 : Int))) - 1)) (counters_2))) ” &&
  “ (DigitHistogramPrefix current_2 exponent n_pre histogram) ” &&
  “ (BucketPlacementProgress current_2 exponent ((i - 1) + 1) histogram (replace_Znth ((Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10)) (((Znth ((Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10)) (counters_2) ((0 : Int))) - 1)) (counters_2)) (replace_Znth (((Znth ((Z.rem (Z.quot (Znth (i) (current_2) ((0 : Int))) exponent) 10)) (counters_2) ((0 : Int))) - 1)) ((Some ((Znth i current_2 (0 : Int))))) (mixed_output_2))) ”
  &&  emp
)

noncomputable def sort_entail_wit_14 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (mixed_output : (List (Option Int))) (counters : (List Int)) (current_2 : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (histogram : (List Int)) (PreH1 : (i < (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) < (Z.quot max_value exponent))) (PreH10 : ((-1) <= i)) (PreH11 : (i < n_pre)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) current_2)) (PreH13 : (Forall ((GE.ge (α := Int)) (999999999)) current_2)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) histogram)) (PreH15 : (Forall ((GE.ge (α := Int)) (n_pre)) histogram)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) counters)) (PreH17 : (Forall ((GE.ge (α := Int)) (n_pre)) counters)) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current_2 exponent)) (PreH21 : (DigitHistogramPrefix current_2 exponent n_pre histogram)) (PreH22 : (BucketPlacementProgress current_2 exponent (i + 1) histogram counters mixed_output)) ,
  (intArray.full a_pre n_pre current_2)
  ** (intArray.full ( &( "count" ) ) 10 counters)
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)
|--
  EX bucket_starts : (List Int), EX working : (List Int), EX pass_output : (List Int), EX current : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) pass_output) ” &&
  “ (Forall ((GE.ge (α := Int)) (999999999)) pass_output) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (StableDigitPass current pass_output exponent) ” &&
  “ (RadixCopyPrefix current pass_output working (0 : Int)) ”
  &&  (intArray.full a_pre n_pre working)
  ** (intArray.full ( &( "count" ) ) 10 bucket_starts)
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre pass_output)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 1000)
) \/
(
forall (n_pre : Int) (input : (List Int)) (mixed_output : (List (Option Int))) (counters : (List Int)) (current_2 : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (histogram : (List Int)) (PreH1 : (i < (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) < (Z.quot max_value exponent))) (PreH10 : ((-1) <= i)) (PreH11 : (i < n_pre)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) current_2)) (PreH13 : (Forall ((GE.ge (α := Int)) (999999999)) current_2)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) histogram)) (PreH15 : (Forall ((GE.ge (α := Int)) (n_pre)) histogram)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) counters)) (PreH17 : (Forall ((GE.ge (α := Int)) (n_pre)) counters)) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current_2 exponent)) (PreH21 : (DigitHistogramPrefix current_2 exponent n_pre histogram)) (PreH22 : (BucketPlacementProgress current_2 exponent (i + 1) histogram counters mixed_output)) ,
  (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)
|--
  EX pass_output : (List Int), EX current : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) pass_output) ” &&
  “ (Forall ((GE.ge (α := Int)) (999999999)) pass_output) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (StableDigitPass current pass_output exponent) ” &&
  “ (RadixCopyPrefix current pass_output current_2 (0 : Int)) ”
  &&  (intArray.seg ( &( "output" ) ) (0 : Int) n_pre pass_output)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 1000)
)

noncomputable def sort_entail_wit_15 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (bucket_starts_2 : (List Int)) (working_2 : (List Int)) (pass_output_2 : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (current_2 : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) pass_output_2)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) pass_output_2)) (PreH13 : (PrefixMaximum input n_pre max_value)) (PreH14 : (DecimalExponent exponent)) (PreH15 : (RadixPassState input current_2 exponent)) (PreH16 : (StableDigitPass current_2 pass_output_2 exponent)) (PreH17 : (RadixCopyPrefix current_2 pass_output_2 working_2 i)) ,
  (intArray.full a_pre n_pre (replace_Znth (i) ((Znth (i - (0 : Int)) pass_output_2 (0 : Int))) (working_2)))
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre pass_output_2)
  ** (intArray.full ( &( "count" ) ) 10 bucket_starts_2)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 1000)
|--
  EX bucket_starts : (List Int), EX working : (List Int), EX pass_output : (List Int), EX current : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) pass_output) ” &&
  “ (Forall ((GE.ge (α := Int)) (999999999)) pass_output) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (StableDigitPass current pass_output exponent) ” &&
  “ (RadixCopyPrefix current pass_output working (i + 1)) ”
  &&  (intArray.full a_pre n_pre working)
  ** (intArray.full ( &( "count" ) ) 10 bucket_starts)
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre pass_output)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 1000)
) \/
(
forall (n_pre : Int) (input : (List Int)) (working_2 : (List Int)) (pass_output_2 : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (current_2 : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) pass_output_2)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) pass_output_2)) (PreH13 : (PrefixMaximum input n_pre max_value)) (PreH14 : (DecimalExponent exponent)) (PreH15 : (RadixPassState input current_2 exponent)) (PreH16 : (StableDigitPass current_2 pass_output_2 exponent)) (PreH17 : (RadixCopyPrefix current_2 pass_output_2 working_2 i)) ,
  TT && emp 
|--
  EX current : (List Int),
  “ ((Zlength (current)) = (Zlength (current_2))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (Zlength (current_2))) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (StableDigitPass current pass_output_2 exponent) ” &&
  “ (RadixCopyPrefix current pass_output_2 (replace_Znth (i) ((Znth (i - (0 : Int)) pass_output_2 (0 : Int))) (working_2)) (i + 1)) ”
  &&  emp
)

noncomputable def sort_entail_wit_16 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (bucket_starts : (List Int)) (working : (List Int)) (pass_output : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (current_2 : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) pass_output)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) pass_output)) (PreH13 : (PrefixMaximum input n_pre max_value)) (PreH14 : (DecimalExponent exponent)) (PreH15 : (RadixPassState input current_2 exponent)) (PreH16 : (StableDigitPass current_2 pass_output exponent)) (PreH17 : (RadixCopyPrefix current_2 pass_output working i)) ,
  (intArray.full a_pre n_pre working)
  ** (intArray.full ( &( "count" ) ) 10 bucket_starts)
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre pass_output)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 1000)
|--
  EX current : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= (exponent * 10)) ” &&
  “ ((exponent * 10) <= 1000000000) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) current) ” &&
  “ (Forall ((GE.ge (α := Int)) (999999999)) current) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent (exponent * 10)) ” &&
  “ (RadixPassState input current (exponent * 10)) ”
  &&  (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
  ** (intArray.undef_full ( &( "count" ) ) 10)
) \/
(
forall (n_pre : Int) (input : (List Int)) (bucket_starts : (List Int)) (working : (List Int)) (pass_output : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (current_2 : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) pass_output)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) pass_output)) (PreH13 : (PrefixMaximum input n_pre max_value)) (PreH14 : (DecimalExponent exponent)) (PreH15 : (RadixPassState input current_2 exponent)) (PreH16 : (StableDigitPass current_2 pass_output exponent)) (PreH17 : (RadixCopyPrefix current_2 pass_output working i)) ,
  (intArray.full ( &( "count" ) ) 10 bucket_starts)
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre pass_output)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 1000)
|--
  “ (RadixPassState input working (exponent * 10)) ” &&
  “ (DecimalExponent (exponent * 10)) ” &&
  “ (Forall ((GE.ge (α := Int)) (999999999)) working) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) working) ”
  &&  (intArray.undef_full ( &( "output" ) ) 1000)
  ** (intArray.undef_full ( &( "count" ) ) 10)
)

noncomputable def sort_entail_wit_16_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (bucket_starts : (List Int)) (working : (List Int)) (pass_output : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (current_2 : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) pass_output)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) pass_output)) (PreH13 : (PrefixMaximum input n_pre max_value)) (PreH14 : (DecimalExponent exponent)) (PreH15 : (RadixPassState input current_2 exponent)) (PreH16 : (StableDigitPass current_2 pass_output exponent)) (PreH17 : (RadixCopyPrefix current_2 pass_output working i)) ,
  (intArray.full ( &( "count" ) ) 10 bucket_starts)
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre pass_output)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 1000)
|--
  “ (RadixPassState input working (exponent * 10)) ”

noncomputable def sort_entail_wit_16_split_goal_2 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (bucket_starts : (List Int)) (working : (List Int)) (pass_output : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (current_2 : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) pass_output)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) pass_output)) (PreH13 : (PrefixMaximum input n_pre max_value)) (PreH14 : (DecimalExponent exponent)) (PreH15 : (RadixPassState input current_2 exponent)) (PreH16 : (StableDigitPass current_2 pass_output exponent)) (PreH17 : (RadixCopyPrefix current_2 pass_output working i)) ,
  (intArray.full ( &( "count" ) ) 10 bucket_starts)
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre pass_output)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 1000)
|--
  “ (DecimalExponent (exponent * 10)) ”

noncomputable def sort_entail_wit_16_split_goal_3 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (bucket_starts : (List Int)) (working : (List Int)) (pass_output : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (current_2 : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) pass_output)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) pass_output)) (PreH13 : (PrefixMaximum input n_pre max_value)) (PreH14 : (DecimalExponent exponent)) (PreH15 : (RadixPassState input current_2 exponent)) (PreH16 : (StableDigitPass current_2 pass_output exponent)) (PreH17 : (RadixCopyPrefix current_2 pass_output working i)) ,
  (intArray.full ( &( "count" ) ) 10 bucket_starts)
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre pass_output)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 1000)
|--
  “ (Forall ((GE.ge (α := Int)) (999999999)) working) ”

noncomputable def sort_entail_wit_16_split_goal_4 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (bucket_starts : (List Int)) (working : (List Int)) (pass_output : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (current_2 : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) pass_output)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) pass_output)) (PreH13 : (PrefixMaximum input n_pre max_value)) (PreH14 : (DecimalExponent exponent)) (PreH15 : (RadixPassState input current_2 exponent)) (PreH16 : (StableDigitPass current_2 pass_output exponent)) (PreH17 : (RadixCopyPrefix current_2 pass_output working i)) ,
  (intArray.full ( &( "count" ) ) 10 bucket_starts)
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre pass_output)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 1000)
|--
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) working) ”

noncomputable def sort_entail_wit_16_split_goal_spatial : Prop :=
  forall (n_pre : Int) (input : (List Int)) (bucket_starts : (List Int)) (working : (List Int)) (pass_output : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (current_2 : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) pass_output)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) pass_output)) (PreH13 : (PrefixMaximum input n_pre max_value)) (PreH14 : (DecimalExponent exponent)) (PreH15 : (RadixPassState input current_2 exponent)) (PreH16 : (StableDigitPass current_2 pass_output exponent)) (PreH17 : (RadixCopyPrefix current_2 pass_output working i)) ,
  (intArray.full ( &( "count" ) ) 10 bucket_starts)
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre pass_output)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 1000)
|--
  (intArray.undef_full ( &( "output" ) ) 1000)
  ** (intArray.undef_full ( &( "count" ) ) 10)

noncomputable def sort_return_wit_1 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (PreH1 : (n_pre <= 1)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH5 : (Forall ((GE.ge (α := Int)) (999999999)) input)) ,
  (intArray.full a_pre n_pre input)
|--
  EX output : (List Int),
  “ (Permutation input output) ” &&
  “ (increasing output) ”
  &&  (intArray.full a_pre n_pre output)
) \/
(
forall (n_pre : Int) (input : (List Int)) (PreH1 : (n_pre <= 1)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH5 : (Forall ((GE.ge (α := Int)) (999999999)) input)) ,
  TT && emp 
|--
  “ (increasing input) ” &&
  “ (Permutation input input) ”
  &&  emp
)

noncomputable def sort_return_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (PreH1 : (n_pre <= 1)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH5 : (Forall ((GE.ge (α := Int)) (999999999)) input)) ,
  (increasing input)

noncomputable def sort_return_wit_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (PreH1 : (n_pre <= 1)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH5 : (Forall ((GE.ge (α := Int)) (999999999)) input)) ,
  (Permutation input input)

noncomputable def sort_return_wit_2 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (current : (List Int)) (exponent : Int) (max_value : Int) (PreH1 : ((Z.quot max_value exponent) <= (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 1000000000)) (PreH8 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH9 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH10 : (PrefixMaximum input n_pre max_value)) (PreH11 : (DecimalExponent exponent)) (PreH12 : (RadixPassState input current exponent)) ,
  (intArray.full a_pre n_pre current)
|--
  EX output : (List Int),
  “ (Permutation input output) ” &&
  “ (increasing output) ”
  &&  (intArray.full a_pre n_pre output)
) \/
(
forall (n_pre : Int) (input : (List Int)) (current : (List Int)) (exponent : Int) (max_value : Int) (PreH1 : ((Z.quot max_value exponent) <= (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 1000000000)) (PreH8 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH9 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH10 : (PrefixMaximum input n_pre max_value)) (PreH11 : (DecimalExponent exponent)) (PreH12 : (RadixPassState input current exponent)) ,
  TT && emp 
|--
  “ (increasing current) ” &&
  “ (Permutation input current) ”
  &&  emp
)

noncomputable def sort_return_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (current : (List Int)) (exponent : Int) (max_value : Int) (PreH1 : ((Z.quot max_value exponent) <= (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 1000000000)) (PreH8 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH9 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH10 : (PrefixMaximum input n_pre max_value)) (PreH11 : (DecimalExponent exponent)) (PreH12 : (RadixPassState input current exponent)) ,
  (increasing current)

noncomputable def sort_return_wit_2_split_goal_2 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (current : (List Int)) (exponent : Int) (max_value : Int) (PreH1 : ((Z.quot max_value exponent) <= (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 1000000000)) (PreH8 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH9 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH10 : (PrefixMaximum input n_pre max_value)) (PreH11 : (DecimalExponent exponent)) (PreH12 : (RadixPassState input current exponent)) ,
  (Permutation input current)

noncomputable def sort_partial_solve_wit_1 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (PreH1 : (n_pre > 1)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH5 : (Forall ((GE.ge (α := Int)) (999999999)) input)) ,
  (intArray.full a_pre n_pre input)
|--
  “ (n_pre > 1) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) input) ” &&
  “ (Forall ((GE.ge (α := Int)) (999999999)) input) ”
  &&  (((a_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((Znth (0 : Int) input (0 : Int))))
  ** (intArray.missing_i a_pre (0 : Int) (0 : Int) n_pre input)

noncomputable def sort_partial_solve_wit_2 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (max_value : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((0 : Int) <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH9 : (Forall ((GE.ge (α := Int)) (999999999)) input)) (PreH10 : (PrefixMaximum input i max_value)) ,
  (intArray.full a_pre n_pre input)
|--
  “ (i < n_pre) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) input) ” &&
  “ (Forall ((GE.ge (α := Int)) (999999999)) input) ” &&
  “ (PrefixMaximum input i max_value) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i input (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre input)

noncomputable def sort_partial_solve_wit_3 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (max_value : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) > max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((0 : Int) <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) input)) (PreH10 : (Forall ((GE.ge (α := Int)) (999999999)) input)) (PreH11 : (PrefixMaximum input i max_value)) ,
  (intArray.full a_pre n_pre input)
|--
  “ ((Znth i input (0 : Int)) > max_value) ” &&
  “ (i < n_pre) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) input) ” &&
  “ (Forall ((GE.ge (α := Int)) (999999999)) input) ” &&
  “ (PrefixMaximum input i max_value) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i input (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre input)

noncomputable def sort_partial_solve_wit_4 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (zero_prefix : (List Int)) (current : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : ((0 : Int) < (Z.quot max_value exponent))) (PreH9 : ((0 : Int) <= digit)) (PreH10 : (digit <= 10)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH13 : (Forall (Eq ((0 : Int))) zero_prefix)) (PreH14 : (PrefixMaximum input n_pre max_value)) (PreH15 : (DecimalExponent exponent)) (PreH16 : (RadixPassState input current exponent)) ,
  (intArray.full a_pre n_pre current)
  ** (intArray.seg ( &( "count" ) ) (0 : Int) digit zero_prefix)
  ** (intArray.undef_seg ( &( "count" ) ) digit 10)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (digit < 10) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((0 : Int) <= digit) ” &&
  “ (digit <= 10) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) current) ” &&
  “ (Forall ((GE.ge (α := Int)) (999999999)) current) ” &&
  “ (Forall (Eq ((0 : Int))) zero_prefix) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ”
  &&  (((( &( "count" ) ) + (digit * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg ( &( "count" ) ) (digit + 1) 10)
  ** (intArray.full a_pre n_pre current)
  ** (intArray.seg ( &( "count" ) ) (0 : Int) digit zero_prefix)
  ** (intArray.undef_full ( &( "output" ) ) 1000)

noncomputable def sort_partial_solve_wit_5 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (counts : (List Int)) (current : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : ((0 : Int) < (Z.quot max_value exponent))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts)) (PreH14 : (Forall ((GE.ge (α := Int)) (i)) counts)) (PreH15 : (PrefixMaximum input n_pre max_value)) (PreH16 : (DecimalExponent exponent)) (PreH17 : (RadixPassState input current exponent)) (PreH18 : (DigitHistogramPrefix current exponent i counts)) ,
  (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 counts)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (i < n_pre) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) current) ” &&
  “ (Forall ((GE.ge (α := Int)) (999999999)) current) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts) ” &&
  “ (Forall ((GE.ge (α := Int)) (i)) counts) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent i counts) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i current (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 counts)
  ** (intArray.undef_full ( &( "output" ) ) 1000)

noncomputable def sort_partial_solve_wit_6 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (current : (List Int)) (counts : (List Int)) (max_value : Int) (exponent : Int) (i : Int) (digit : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= max_value)) (PreH4 : (max_value <= 999999999)) (PreH5 : (1 <= exponent)) (PreH6 : (exponent <= 100000000)) (PreH7 : ((0 : Int) < (Z.quot max_value exponent))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH11 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts)) (PreH13 : (Forall ((GE.ge (α := Int)) (i)) counts)) (PreH14 : (PrefixMaximum input n_pre max_value)) (PreH15 : (DecimalExponent exponent)) (PreH16 : (RadixPassState input current exponent)) (PreH17 : (DigitHistogramPrefix current exponent i counts)) (PreH18 : (digit = (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10))) (PreH19 : ((0 : Int) <= digit)) (PreH20 : (digit < 10)) ,
  (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 counts)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) current) ” &&
  “ (Forall ((GE.ge (α := Int)) (999999999)) current) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts) ” &&
  “ (Forall ((GE.ge (α := Int)) (i)) counts) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent i counts) ” &&
  “ (digit = (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) ” &&
  “ ((0 : Int) <= digit) ” &&
  “ (digit < 10) ”
  &&  (((( &( "count" ) ) + (digit * sizeof(INT)))) # Int |-> ((Znth digit counts (0 : Int))))
  ** (intArray.missing_i ( &( "count" ) ) digit (0 : Int) 10 counts)
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)

noncomputable def sort_partial_solve_wit_7 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (current : (List Int)) (counts : (List Int)) (max_value : Int) (exponent : Int) (i : Int) (digit : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= max_value)) (PreH4 : (max_value <= 999999999)) (PreH5 : (1 <= exponent)) (PreH6 : (exponent <= 100000000)) (PreH7 : ((0 : Int) < (Z.quot max_value exponent))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH11 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts)) (PreH13 : (Forall ((GE.ge (α := Int)) (i)) counts)) (PreH14 : (PrefixMaximum input n_pre max_value)) (PreH15 : (DecimalExponent exponent)) (PreH16 : (RadixPassState input current exponent)) (PreH17 : (DigitHistogramPrefix current exponent i counts)) (PreH18 : (digit = (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10))) (PreH19 : ((0 : Int) <= digit)) (PreH20 : (digit < 10)) ,
  (intArray.full ( &( "count" ) ) 10 counts)
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) current) ” &&
  “ (Forall ((GE.ge (α := Int)) (999999999)) current) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts) ” &&
  “ (Forall ((GE.ge (α := Int)) (i)) counts) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent i counts) ” &&
  “ (digit = (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) ” &&
  “ ((0 : Int) <= digit) ” &&
  “ (digit < 10) ”
  &&  (((( &( "count" ) ) + (digit * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i ( &( "count" ) ) digit (0 : Int) 10 counts)
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)

noncomputable def sort_partial_solve_wit_8 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (totals : (List Int)) (current : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (histogram : (List Int)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) < (Z.quot max_value exponent))) (PreH10 : (1 <= digit)) (PreH11 : (digit <= 10)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH13 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) histogram)) (PreH15 : (Forall ((GE.ge (α := Int)) (n_pre)) histogram)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) totals)) (PreH17 : (Forall ((GE.ge (α := Int)) (n_pre)) totals)) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current exponent)) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH22 : (DigitPrefixTotals histogram totals digit)) ,
  (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 totals)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (digit < 10) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (histogram)) = 10) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ (1 <= digit) ” &&
  “ (digit <= 10) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) current) ” &&
  “ (Forall ((GE.ge (α := Int)) (999999999)) current) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) histogram) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) histogram) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) totals) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) totals) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent n_pre histogram) ” &&
  “ (DigitPrefixTotals histogram totals digit) ”
  &&  (((( &( "count" ) ) + (digit * sizeof(INT)))) # Int |-> ((Znth digit totals (0 : Int))))
  ** (intArray.missing_i ( &( "count" ) ) digit (0 : Int) 10 totals)
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)

noncomputable def sort_partial_solve_wit_9 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (totals : (List Int)) (current : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (histogram : (List Int)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) < (Z.quot max_value exponent))) (PreH10 : (1 <= digit)) (PreH11 : (digit <= 10)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH13 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) histogram)) (PreH15 : (Forall ((GE.ge (α := Int)) (n_pre)) histogram)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) totals)) (PreH17 : (Forall ((GE.ge (α := Int)) (n_pre)) totals)) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current exponent)) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH22 : (DigitPrefixTotals histogram totals digit)) ,
  (intArray.full ( &( "count" ) ) 10 totals)
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (digit < 10) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (histogram)) = 10) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ (1 <= digit) ” &&
  “ (digit <= 10) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) current) ” &&
  “ (Forall ((GE.ge (α := Int)) (999999999)) current) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) histogram) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) histogram) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) totals) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) totals) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent n_pre histogram) ” &&
  “ (DigitPrefixTotals histogram totals digit) ”
  &&  (((( &( "count" ) ) + ((digit - 1) * sizeof(INT)))) # Int |-> ((Znth (digit - 1) totals (0 : Int))))
  ** (intArray.missing_i ( &( "count" ) ) (digit - 1) (0 : Int) 10 totals)
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)

noncomputable def sort_partial_solve_wit_10 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (totals : (List Int)) (current : (List Int)) (digit : Int) (exponent : Int) (max_value : Int) (histogram : (List Int)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) < (Z.quot max_value exponent))) (PreH10 : (1 <= digit)) (PreH11 : (digit <= 10)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH13 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) histogram)) (PreH15 : (Forall ((GE.ge (α := Int)) (n_pre)) histogram)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) totals)) (PreH17 : (Forall ((GE.ge (α := Int)) (n_pre)) totals)) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current exponent)) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH22 : (DigitPrefixTotals histogram totals digit)) ,
  (intArray.full ( &( "count" ) ) 10 totals)
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)
|--
  “ (digit < 10) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (histogram)) = 10) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ (1 <= digit) ” &&
  “ (digit <= 10) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) current) ” &&
  “ (Forall ((GE.ge (α := Int)) (999999999)) current) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) histogram) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) histogram) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) totals) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) totals) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent n_pre histogram) ” &&
  “ (DigitPrefixTotals histogram totals digit) ”
  &&  (((( &( "count" ) ) + (digit * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i ( &( "count" ) ) digit (0 : Int) 10 totals)
  ** (intArray.full a_pre n_pre current)
  ** (intArray.undef_full ( &( "output" ) ) 1000)

noncomputable def sort_partial_solve_wit_11 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (mixed_output : (List (Option Int))) (counters : (List Int)) (current : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (histogram : (List Int)) (PreH1 : (i >= (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (histogram)) = 10)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) < (Z.quot max_value exponent))) (PreH10 : ((-1) <= i)) (PreH11 : (i < n_pre)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH13 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) histogram)) (PreH15 : (Forall ((GE.ge (α := Int)) (n_pre)) histogram)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) counters)) (PreH17 : (Forall ((GE.ge (α := Int)) (n_pre)) counters)) (PreH18 : (PrefixMaximum input n_pre max_value)) (PreH19 : (DecimalExponent exponent)) (PreH20 : (RadixPassState input current exponent)) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH22 : (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output)) ,
  (intArray.full a_pre n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 counters)
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)
|--
  “ (i >= (0 : Int)) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (histogram)) = 10) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((-1) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) current) ” &&
  “ (Forall ((GE.ge (α := Int)) (999999999)) current) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) histogram) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) histogram) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counters) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) counters) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent n_pre histogram) ” &&
  “ (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i current (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre current)
  ** (intArray.full ( &( "count" ) ) 10 counters)
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)

noncomputable def sort_partial_solve_wit_12 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (current : (List Int)) (histogram : (List Int)) (counters : (List Int)) (mixed_output : (List (Option Int))) (max_value : Int) (exponent : Int) (i : Int) (digit : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (histogram)) = 10)) (PreH4 : ((0 : Int) <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : ((0 : Int) < (Z.quot max_value exponent))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) histogram)) (PreH14 : (Forall ((GE.ge (α := Int)) (n_pre)) histogram)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) counters)) (PreH16 : (Forall ((GE.ge (α := Int)) (n_pre)) counters)) (PreH17 : (PrefixMaximum input n_pre max_value)) (PreH18 : (DecimalExponent exponent)) (PreH19 : (RadixPassState input current exponent)) (PreH20 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH21 : (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output)) (PreH22 : (digit = (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10))) (PreH23 : ((0 : Int) <= digit)) (PreH24 : (digit < 10)) (PreH25 : (1 <= (Znth (digit) (counters) ((0 : Int))))) (PreH26 : ((Znth (digit) (counters) ((0 : Int))) <= n_pre)) ,
  (intArray.full a_pre n_pre current)
  ** (((( &( "count" ) ) + (digit * sizeof(INT)))) # Int |-> (((Znth (digit) (counters) ((0 : Int))) - 1)))
  ** (intArray.missing_i ( &( "count" ) ) digit (0 : Int) 10 counters)
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (histogram)) = 10) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) current) ” &&
  “ (Forall ((GE.ge (α := Int)) (999999999)) current) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) histogram) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) histogram) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counters) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) counters) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent n_pre histogram) ” &&
  “ (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output) ” &&
  “ (digit = (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) ” &&
  “ ((0 : Int) <= digit) ” &&
  “ (digit < 10) ” &&
  “ (1 <= (Znth (digit) (counters) ((0 : Int)))) ” &&
  “ ((Znth (digit) (counters) ((0 : Int))) <= n_pre) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i current (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre current)
  ** (((( &( "count" ) ) + (digit * sizeof(INT)))) # Int |-> (((Znth (digit) (counters) ((0 : Int))) - 1)))
  ** (intArray.missing_i ( &( "count" ) ) digit (0 : Int) 10 counters)
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)

noncomputable def sort_partial_solve_wit_13 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (current : (List Int)) (histogram : (List Int)) (counters : (List Int)) (mixed_output : (List (Option Int))) (max_value : Int) (exponent : Int) (i : Int) (digit : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (histogram)) = 10)) (PreH4 : ((0 : Int) <= max_value)) (PreH5 : (max_value <= 999999999)) (PreH6 : (1 <= exponent)) (PreH7 : (exponent <= 100000000)) (PreH8 : ((0 : Int) < (Z.quot max_value exponent))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i < n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) current)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) current)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) histogram)) (PreH14 : (Forall ((GE.ge (α := Int)) (n_pre)) histogram)) (PreH15 : (Forall ((LE.le (α := Int)) ((0 : Int))) counters)) (PreH16 : (Forall ((GE.ge (α := Int)) (n_pre)) counters)) (PreH17 : (PrefixMaximum input n_pre max_value)) (PreH18 : (DecimalExponent exponent)) (PreH19 : (RadixPassState input current exponent)) (PreH20 : (DigitHistogramPrefix current exponent n_pre histogram)) (PreH21 : (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output)) (PreH22 : (digit = (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10))) (PreH23 : ((0 : Int) <= digit)) (PreH24 : (digit < 10)) (PreH25 : (1 <= (Znth (digit) (counters) ((0 : Int))))) (PreH26 : ((Znth (digit) (counters) ((0 : Int))) <= n_pre)) ,
  (intArray.full ( &( "count" ) ) 10 (replace_Znth (digit) (((Znth (digit) (counters) ((0 : Int))) - 1)) (counters)))
  ** (intArray.full a_pre n_pre current)
  ** (intArray.mixed_full ( &( "output" ) ) 1000 mixed_output)
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (histogram)) = 10) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) < (Z.quot max_value exponent)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) current) ” &&
  “ (Forall ((GE.ge (α := Int)) (999999999)) current) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) histogram) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) histogram) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counters) ” &&
  “ (Forall ((GE.ge (α := Int)) (n_pre)) counters) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (DigitHistogramPrefix current exponent n_pre histogram) ” &&
  “ (BucketPlacementProgress current exponent (i + 1) histogram counters mixed_output) ” &&
  “ (digit = (Z.rem (Z.quot (Znth (i) (current) ((0 : Int))) exponent) 10)) ” &&
  “ ((0 : Int) <= digit) ” &&
  “ (digit < 10) ” &&
  “ (1 <= (Znth (digit) (counters) ((0 : Int)))) ” &&
  “ ((Znth (digit) (counters) ((0 : Int))) <= n_pre) ”
  &&  (((( &( "output" ) ) + (((Znth (digit) (counters) ((0 : Int))) - 1) * sizeof(INT)))) # Int |->_)
  ** (intArray.mixed_missing_i ( &( "output" ) ) ((Znth (digit) (counters) ((0 : Int))) - 1) (0 : Int) 1000 mixed_output)
  ** (intArray.full ( &( "count" ) ) 10 (replace_Znth (digit) (((Znth (digit) (counters) ((0 : Int))) - 1)) (counters)))
  ** (intArray.full a_pre n_pre current)

noncomputable def sort_partial_solve_wit_14 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (bucket_starts : (List Int)) (working : (List Int)) (pass_output : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (current : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (current)) = n_pre)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) pass_output)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) pass_output)) (PreH13 : (PrefixMaximum input n_pre max_value)) (PreH14 : (DecimalExponent exponent)) (PreH15 : (RadixPassState input current exponent)) (PreH16 : (StableDigitPass current pass_output exponent)) (PreH17 : (RadixCopyPrefix current pass_output working i)) ,
  (intArray.full a_pre n_pre working)
  ** (intArray.full ( &( "count" ) ) 10 bucket_starts)
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre pass_output)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 1000)
|--
  “ (i < n_pre) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) pass_output) ” &&
  “ (Forall ((GE.ge (α := Int)) (999999999)) pass_output) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (StableDigitPass current pass_output exponent) ” &&
  “ (RadixCopyPrefix current pass_output working i) ”
  &&  (((( &( "output" ) ) + (i * sizeof(INT)))) # Int |-> ((Znth (i - (0 : Int)) pass_output (0 : Int))))
  ** (intArray.missing_i ( &( "output" ) ) i (0 : Int) n_pre pass_output)
  ** (intArray.full a_pre n_pre working)
  ** (intArray.full ( &( "count" ) ) 10 bucket_starts)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 1000)

noncomputable def sort_partial_solve_wit_15 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (bucket_starts : (List Int)) (working : (List Int)) (pass_output : (List Int)) (i : Int) (exponent : Int) (max_value : Int) (current : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (current)) = n_pre)) (PreH5 : ((0 : Int) <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) pass_output)) (PreH12 : (Forall ((GE.ge (α := Int)) (999999999)) pass_output)) (PreH13 : (PrefixMaximum input n_pre max_value)) (PreH14 : (DecimalExponent exponent)) (PreH15 : (RadixPassState input current exponent)) (PreH16 : (StableDigitPass current pass_output exponent)) (PreH17 : (RadixCopyPrefix current pass_output working i)) ,
  (intArray.seg ( &( "output" ) ) (0 : Int) n_pre pass_output)
  ** (intArray.full a_pre n_pre working)
  ** (intArray.full ( &( "count" ) ) 10 bucket_starts)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 1000)
|--
  “ (i < n_pre) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (current)) = n_pre) ” &&
  “ ((0 : Int) <= max_value) ” &&
  “ (max_value <= 999999999) ” &&
  “ (1 <= exponent) ” &&
  “ (exponent <= 100000000) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) pass_output) ” &&
  “ (Forall ((GE.ge (α := Int)) (999999999)) pass_output) ” &&
  “ (PrefixMaximum input n_pre max_value) ” &&
  “ (DecimalExponent exponent) ” &&
  “ (RadixPassState input current exponent) ” &&
  “ (StableDigitPass current pass_output exponent) ” &&
  “ (RadixCopyPrefix current pass_output working i) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i a_pre i (0 : Int) n_pre working)
  ** (intArray.seg ( &( "output" ) ) (0 : Int) n_pre pass_output)
  ** (intArray.full ( &( "count" ) ) 10 bucket_starts)
  ** (intArray.undef_seg ( &( "output" ) ) n_pre 1000)


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
  proof_of_sort_safety_wit_10 : sort_safety_wit_10
  proof_of_sort_safety_wit_11 : sort_safety_wit_11
  proof_of_sort_safety_wit_12 : sort_safety_wit_12
  proof_of_sort_safety_wit_13 : sort_safety_wit_13
  proof_of_sort_safety_wit_14 : sort_safety_wit_14
  proof_of_sort_safety_wit_15 : sort_safety_wit_15
  proof_of_sort_safety_wit_16 : sort_safety_wit_16
  proof_of_sort_safety_wit_18 : sort_safety_wit_18
  proof_of_sort_safety_wit_19 : sort_safety_wit_19
  proof_of_sort_safety_wit_20 : sort_safety_wit_20
  proof_of_sort_safety_wit_22 : sort_safety_wit_22
  proof_of_sort_safety_wit_23 : sort_safety_wit_23
  proof_of_sort_safety_wit_24 : sort_safety_wit_24
  proof_of_sort_safety_wit_25 : sort_safety_wit_25
  proof_of_sort_safety_wit_26 : sort_safety_wit_26
  proof_of_sort_safety_wit_27 : sort_safety_wit_27
  proof_of_sort_safety_wit_28 : sort_safety_wit_28
  proof_of_sort_safety_wit_29 : sort_safety_wit_29
  proof_of_sort_safety_wit_30 : sort_safety_wit_30
  proof_of_sort_safety_wit_31 : sort_safety_wit_31
  proof_of_sort_safety_wit_32 : sort_safety_wit_32
  proof_of_sort_safety_wit_33 : sort_safety_wit_33
  proof_of_sort_safety_wit_34 : sort_safety_wit_34
  proof_of_sort_safety_wit_35 : sort_safety_wit_35
  proof_of_sort_safety_wit_36 : sort_safety_wit_36
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
  proof_of_sort_partial_solve_wit_15 : sort_partial_solve_wit_15
  proof_of_sort_safety_wit_17 : sort_safety_wit_17
  proof_of_sort_safety_wit_21 : sort_safety_wit_21
  proof_of_sort_entail_wit_1 : sort_entail_wit_1
  proof_of_sort_entail_wit_2_1 : sort_entail_wit_2_1
  proof_of_sort_entail_wit_2_2 : sort_entail_wit_2_2
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
  proof_of_sort_entail_wit_15 : sort_entail_wit_15
  proof_of_sort_entail_wit_16 : sort_entail_wit_16
  proof_of_sort_return_wit_1 : sort_return_wit_1
  proof_of_sort_return_wit_2 : sort_return_wit_2

end SimpleC.EE.LLM_bench.Algorithms.bucket_sort.bucket_sort_goal
