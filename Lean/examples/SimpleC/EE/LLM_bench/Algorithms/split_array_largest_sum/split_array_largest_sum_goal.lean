import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.split_array_largest_sum.split_array_largest_sum_lib
open SimpleC.EE.LLM_bench.Algorithms.split_array_largest_sum.split_array_largest_sum_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.split_array_largest_sum.split_array_largest_sum_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance split_array_largest_sum_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def check_safety_wit_1 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= n_pre)) (PreH5 : ((0 : Int) <= cap_pre)) (PreH6 : (cap_pre <= 1000000000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH9 : (Forall ((GT.gt (α := Int)) (100000000)) l)) ,
  ((( &( "cnt" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "cap" ) )) # Int |-> (cap_pre))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def check_safety_wit_2 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= n_pre)) (PreH5 : ((0 : Int) <= cap_pre)) (PreH6 : (cap_pre <= 1000000000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH9 : (Forall ((GT.gt (α := Int)) (100000000)) l)) ,
  ((( &( "cur" ) )) # Int |->_)
  ** ((( &( "cnt" ) )) # Int |-> (1))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "cap" ) )) # Int |-> (cap_pre))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def check_safety_wit_3 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= n_pre)) (PreH5 : ((0 : Int) <= cap_pre)) (PreH6 : (cap_pre <= 1000000000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH9 : (Forall ((GT.gt (α := Int)) (100000000)) l)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "cur" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "cnt" ) )) # Int |-> (1))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "cap" ) )) # Int |-> (cap_pre))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def check_safety_wit_4 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : ((Znth i l (0 : Int)) > cap_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : ((0 : Int) <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH11 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= cnt)) (PreH15 : (cnt <= (i + 1))) (PreH16 : ((0 : Int) <= cur)) (PreH17 : (cur <= cap_pre)) (PreH18 : (SplitProgress (sublist ((0 : Int)) (i) (l)) cap_pre cnt cur)) ,
  (intArray.full arr_pre n_pre l)
  ** ((( &( "x" ) )) # Int |-> ((Znth i l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "cap" ) )) # Int |-> (cap_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "cur" ) )) # Int |-> (cur))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def check_safety_wit_5 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : ((Znth i l (0 : Int)) <= cap_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : ((0 : Int) <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH11 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= cnt)) (PreH15 : (cnt <= (i + 1))) (PreH16 : ((0 : Int) <= cur)) (PreH17 : (cur <= cap_pre)) (PreH18 : (SplitProgress (sublist ((0 : Int)) (i) (l)) cap_pre cnt cur)) ,
  (intArray.full arr_pre n_pre l)
  ** ((( &( "x" ) )) # Int |-> ((Znth i l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "cap" ) )) # Int |-> (cap_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "cur" ) )) # Int |-> (cur))
|--
  “ ((cur + (Znth i l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (cur + (Znth i l (0 : Int)))) ”

noncomputable def check_safety_wit_6 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : ((cur + (Znth i l (0 : Int))) > cap_pre)) (PreH2 : ((Znth i l (0 : Int)) <= cap_pre)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : ((0 : Int) <= cap_pre)) (PreH9 : (cap_pre <= 1000000000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH12 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (1 <= cnt)) (PreH16 : (cnt <= (i + 1))) (PreH17 : ((0 : Int) <= cur)) (PreH18 : (cur <= cap_pre)) (PreH19 : (SplitProgress (sublist ((0 : Int)) (i) (l)) cap_pre cnt cur)) ,
  (intArray.full arr_pre n_pre l)
  ** ((( &( "x" ) )) # Int |-> ((Znth i l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "cap" ) )) # Int |-> (cap_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "cur" ) )) # Int |-> (cur))
|--
  “ ((cnt + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (cnt + 1)) ”

noncomputable def check_safety_wit_7 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : ((cur + (Znth i l (0 : Int))) > cap_pre)) (PreH2 : ((Znth i l (0 : Int)) <= cap_pre)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : ((0 : Int) <= cap_pre)) (PreH9 : (cap_pre <= 1000000000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH12 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (1 <= cnt)) (PreH16 : (cnt <= (i + 1))) (PreH17 : ((0 : Int) <= cur)) (PreH18 : (cur <= cap_pre)) (PreH19 : (SplitProgress (sublist ((0 : Int)) (i) (l)) cap_pre cnt cur)) ,
  (intArray.full arr_pre n_pre l)
  ** ((( &( "x" ) )) # Int |-> ((Znth i l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "cap" ) )) # Int |-> (cap_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "cur" ) )) # Int |-> (cur))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def check_safety_wit_8 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : ((cur + (Znth i l (0 : Int))) <= cap_pre)) (PreH2 : ((Znth i l (0 : Int)) <= cap_pre)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : ((0 : Int) <= cap_pre)) (PreH9 : (cap_pre <= 1000000000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH12 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (1 <= cnt)) (PreH16 : (cnt <= (i + 1))) (PreH17 : ((0 : Int) <= cur)) (PreH18 : (cur <= cap_pre)) (PreH19 : (SplitProgress (sublist ((0 : Int)) (i) (l)) cap_pre cnt cur)) ,
  (intArray.full arr_pre n_pre l)
  ** ((( &( "x" ) )) # Int |-> ((Znth i l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "cap" ) )) # Int |-> (cap_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "cur" ) )) # Int |-> (cur))
|--
  “ ((cur + (Znth i l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (cur + (Znth i l (0 : Int)))) ”

noncomputable def check_safety_wit_9 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : ((cur + (Znth i l (0 : Int))) > cap_pre)) (PreH2 : ((Znth i l (0 : Int)) <= cap_pre)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : ((0 : Int) <= cap_pre)) (PreH9 : (cap_pre <= 1000000000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH12 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (1 <= cnt)) (PreH16 : (cnt <= (i + 1))) (PreH17 : ((0 : Int) <= cur)) (PreH18 : (cur <= cap_pre)) (PreH19 : (SplitProgress (sublist ((0 : Int)) (i) (l)) cap_pre cnt cur)) ,
  (intArray.full arr_pre n_pre l)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "cap" ) )) # Int |-> (cap_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cnt" ) )) # Int |-> ((cnt + 1)))
  ** ((( &( "cur" ) )) # Int |-> ((Znth i l (0 : Int))))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def check_safety_wit_10 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : ((cur + (Znth i l (0 : Int))) <= cap_pre)) (PreH2 : ((Znth i l (0 : Int)) <= cap_pre)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : ((0 : Int) <= cap_pre)) (PreH9 : (cap_pre <= 1000000000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH12 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (1 <= cnt)) (PreH16 : (cnt <= (i + 1))) (PreH17 : ((0 : Int) <= cur)) (PreH18 : (cur <= cap_pre)) (PreH19 : (SplitProgress (sublist ((0 : Int)) (i) (l)) cap_pre cnt cur)) ,
  (intArray.full arr_pre n_pre l)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "cap" ) )) # Int |-> (cap_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "cur" ) )) # Int |-> ((cur + (Znth i l (0 : Int)))))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def check_safety_wit_11 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : (cnt <= m_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : ((0 : Int) <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH11 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= cnt)) (PreH15 : (cnt <= (i + 1))) (PreH16 : ((0 : Int) <= cur)) (PreH17 : (cur <= cap_pre)) (PreH18 : (SplitProgress (sublist ((0 : Int)) (i) (l)) cap_pre cnt cur)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "cap" ) )) # Int |-> (cap_pre))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "cur" ) )) # Int |-> (cur))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def check_safety_wit_12 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : (cnt > m_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : ((0 : Int) <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH11 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= cnt)) (PreH15 : (cnt <= (i + 1))) (PreH16 : ((0 : Int) <= cur)) (PreH17 : (cur <= cap_pre)) (PreH18 : (SplitProgress (sublist ((0 : Int)) (i) (l)) cap_pre cnt cur)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "cap" ) )) # Int |-> (cap_pre))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "cur" ) )) # Int |-> (cur))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def check_entail_wit_1 : Prop :=
  (
forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= n_pre)) (PreH5 : ((0 : Int) <= cap_pre)) (PreH6 : (cap_pre <= 1000000000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH9 : (Forall ((GT.gt (α := Int)) (100000000)) l)) ,
  (intArray.full arr_pre n_pre l)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= n_pre) ” &&
  “ ((0 : Int) <= cap_pre) ” &&
  “ (cap_pre <= 1000000000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GT.gt (α := Int)) (100000000)) l) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= ((0 : Int) + 1)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= cap_pre) ” &&
  “ (SplitProgress (sublist ((0 : Int)) ((0 : Int)) (l)) cap_pre 1 (0 : Int)) ”
  &&  (intArray.full arr_pre n_pre l)
) \/
(
forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= n_pre)) (PreH5 : ((0 : Int) <= cap_pre)) (PreH6 : (cap_pre <= 1000000000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH9 : (Forall ((GT.gt (α := Int)) (100000000)) l)) ,
  TT && emp 
|--
  “ (SplitProgress (sublist ((0 : Int)) ((0 : Int)) (l)) cap_pre 1 (0 : Int)) ”
  &&  emp
)

noncomputable def check_entail_wit_1_split_goal_1 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= n_pre)) (PreH5 : ((0 : Int) <= cap_pre)) (PreH6 : (cap_pre <= 1000000000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH9 : (Forall ((GT.gt (α := Int)) (100000000)) l)) ,
  (SplitProgress (sublist ((0 : Int)) ((0 : Int)) (l)) cap_pre 1 (0 : Int))

noncomputable def check_entail_wit_2_1 : Prop :=
  (
forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : ((cur + (Znth i l (0 : Int))) > cap_pre)) (PreH2 : ((Znth i l (0 : Int)) <= cap_pre)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : ((0 : Int) <= cap_pre)) (PreH9 : (cap_pre <= 1000000000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH12 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (1 <= cnt)) (PreH16 : (cnt <= (i + 1))) (PreH17 : ((0 : Int) <= cur)) (PreH18 : (cur <= cap_pre)) (PreH19 : (SplitProgress (sublist ((0 : Int)) (i) (l)) cap_pre cnt cur)) ,
  (intArray.full arr_pre n_pre l)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= n_pre) ” &&
  “ ((0 : Int) <= cap_pre) ” &&
  “ (cap_pre <= 1000000000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GT.gt (α := Int)) (100000000)) l) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ (1 <= (cnt + 1)) ” &&
  “ ((cnt + 1) <= ((i + 1) + 1)) ” &&
  “ ((0 : Int) <= (Znth i l (0 : Int))) ” &&
  “ ((Znth i l (0 : Int)) <= cap_pre) ” &&
  “ (SplitProgress (sublist ((0 : Int)) ((i + 1)) (l)) cap_pre (cnt + 1) (Znth i l (0 : Int))) ”
  &&  (intArray.full arr_pre n_pre l)
) \/
(
forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : ((cur + (Znth i l (0 : Int))) > cap_pre)) (PreH2 : ((Znth i l (0 : Int)) <= cap_pre)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : ((0 : Int) <= cap_pre)) (PreH9 : (cap_pre <= 1000000000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH12 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (1 <= cnt)) (PreH16 : (cnt <= (i + 1))) (PreH17 : ((0 : Int) <= cur)) (PreH18 : (cur <= cap_pre)) (PreH19 : (SplitProgress (sublist ((0 : Int)) (i) (l)) cap_pre cnt cur)) ,
  TT && emp 
|--
  “ (SplitProgress (sublist ((0 : Int)) ((i + 1)) (l)) cap_pre (cnt + 1) (Znth i l (0 : Int))) ”
  &&  emp
)

noncomputable def check_entail_wit_2_1_split_goal_1 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : ((cur + (Znth i l (0 : Int))) > cap_pre)) (PreH2 : ((Znth i l (0 : Int)) <= cap_pre)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : ((0 : Int) <= cap_pre)) (PreH9 : (cap_pre <= 1000000000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH12 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (1 <= cnt)) (PreH16 : (cnt <= (i + 1))) (PreH17 : ((0 : Int) <= cur)) (PreH18 : (cur <= cap_pre)) (PreH19 : (SplitProgress (sublist ((0 : Int)) (i) (l)) cap_pre cnt cur)) ,
  (SplitProgress (sublist ((0 : Int)) ((i + 1)) (l)) cap_pre (cnt + 1) (Znth i l (0 : Int)))

noncomputable def check_entail_wit_2_2 : Prop :=
  (
forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : ((cur + (Znth i l (0 : Int))) <= cap_pre)) (PreH2 : ((Znth i l (0 : Int)) <= cap_pre)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : ((0 : Int) <= cap_pre)) (PreH9 : (cap_pre <= 1000000000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH12 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (1 <= cnt)) (PreH16 : (cnt <= (i + 1))) (PreH17 : ((0 : Int) <= cur)) (PreH18 : (cur <= cap_pre)) (PreH19 : (SplitProgress (sublist ((0 : Int)) (i) (l)) cap_pre cnt cur)) ,
  (intArray.full arr_pre n_pre l)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= n_pre) ” &&
  “ ((0 : Int) <= cap_pre) ” &&
  “ (cap_pre <= 1000000000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GT.gt (α := Int)) (100000000)) l) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ (1 <= cnt) ” &&
  “ (cnt <= ((i + 1) + 1)) ” &&
  “ ((0 : Int) <= (cur + (Znth i l (0 : Int)))) ” &&
  “ ((cur + (Znth i l (0 : Int))) <= cap_pre) ” &&
  “ (SplitProgress (sublist ((0 : Int)) ((i + 1)) (l)) cap_pre cnt (cur + (Znth i l (0 : Int)))) ”
  &&  (intArray.full arr_pre n_pre l)
) \/
(
forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : ((cur + (Znth i l (0 : Int))) <= cap_pre)) (PreH2 : ((Znth i l (0 : Int)) <= cap_pre)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : ((0 : Int) <= cap_pre)) (PreH9 : (cap_pre <= 1000000000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH12 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (1 <= cnt)) (PreH16 : (cnt <= (i + 1))) (PreH17 : ((0 : Int) <= cur)) (PreH18 : (cur <= cap_pre)) (PreH19 : (SplitProgress (sublist ((0 : Int)) (i) (l)) cap_pre cnt cur)) ,
  TT && emp 
|--
  “ (SplitProgress (sublist ((0 : Int)) ((i + 1)) (l)) cap_pre cnt (cur + (Znth i l (0 : Int)))) ” &&
  “ ((0 : Int) <= (cur + (Znth i l (0 : Int)))) ”
  &&  emp
)

noncomputable def check_entail_wit_2_2_split_goal_1 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : ((cur + (Znth i l (0 : Int))) <= cap_pre)) (PreH2 : ((Znth i l (0 : Int)) <= cap_pre)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : ((0 : Int) <= cap_pre)) (PreH9 : (cap_pre <= 1000000000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH12 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (1 <= cnt)) (PreH16 : (cnt <= (i + 1))) (PreH17 : ((0 : Int) <= cur)) (PreH18 : (cur <= cap_pre)) (PreH19 : (SplitProgress (sublist ((0 : Int)) (i) (l)) cap_pre cnt cur)) ,
  (SplitProgress (sublist ((0 : Int)) ((i + 1)) (l)) cap_pre cnt (cur + (Znth i l (0 : Int))))

noncomputable def check_entail_wit_2_2_split_goal_2 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : ((cur + (Znth i l (0 : Int))) <= cap_pre)) (PreH2 : ((Znth i l (0 : Int)) <= cap_pre)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= n_pre)) (PreH8 : ((0 : Int) <= cap_pre)) (PreH9 : (cap_pre <= 1000000000)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH12 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (1 <= cnt)) (PreH16 : (cnt <= (i + 1))) (PreH17 : ((0 : Int) <= cur)) (PreH18 : (cur <= cap_pre)) (PreH19 : (SplitProgress (sublist ((0 : Int)) (i) (l)) cap_pre cnt cur)) ,
  ((0 : Int) <= (cur + (Znth i l (0 : Int))))

noncomputable def check_return_wit_1 : Prop :=
  (
forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : (cnt > m_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : ((0 : Int) <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH11 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= cnt)) (PreH15 : (cnt <= (i + 1))) (PreH16 : ((0 : Int) <= cur)) (PreH17 : (cur <= cap_pre)) (PreH18 : (SplitProgress (sublist ((0 : Int)) (i) (l)) cap_pre cnt cur)) ,
  (intArray.full arr_pre n_pre l)
|--
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 1) ” &&
  “ (((0 : Int) = 1) -> (SplitFeasible l m_pre cap_pre)) ” &&
  “ (((0 : Int) = (0 : Int)) -> (SplitInfeasible l m_pre cap_pre)) ”
  &&  (intArray.full arr_pre n_pre l)
) \/
(
forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : (cnt > m_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : ((0 : Int) <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH11 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= cnt)) (PreH15 : (cnt <= (i + 1))) (PreH16 : ((0 : Int) <= cur)) (PreH17 : (cur <= cap_pre)) (PreH18 : (SplitProgress (sublist ((0 : Int)) (i) (l)) cap_pre cnt cur)) ,
  TT && emp 
|--
  “ (((0 : Int) = (0 : Int)) -> (SplitInfeasible l m_pre cap_pre)) ”
  &&  emp
)

noncomputable def check_return_wit_1_split_goal_1 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : (cnt > m_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : ((0 : Int) <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH11 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= cnt)) (PreH15 : (cnt <= (i + 1))) (PreH16 : ((0 : Int) <= cur)) (PreH17 : (cur <= cap_pre)) (PreH18 : (SplitProgress (sublist ((0 : Int)) (i) (l)) cap_pre cnt cur)) ,
  (((0 : Int) = (0 : Int)) -> (SplitInfeasible l m_pre cap_pre))

noncomputable def check_return_wit_2 : Prop :=
  (
forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : (cnt <= m_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : ((0 : Int) <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH11 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= cnt)) (PreH15 : (cnt <= (i + 1))) (PreH16 : ((0 : Int) <= cur)) (PreH17 : (cur <= cap_pre)) (PreH18 : (SplitProgress (sublist ((0 : Int)) (i) (l)) cap_pre cnt cur)) ,
  (intArray.full arr_pre n_pre l)
|--
  “ ((0 : Int) <= 1) ” &&
  “ (1 <= 1) ” &&
  “ ((1 = 1) -> (SplitFeasible l m_pre cap_pre)) ” &&
  “ ((1 = (0 : Int)) -> (SplitInfeasible l m_pre cap_pre)) ”
  &&  (intArray.full arr_pre n_pre l)
) \/
(
forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : (cnt <= m_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : ((0 : Int) <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH11 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= cnt)) (PreH15 : (cnt <= (i + 1))) (PreH16 : ((0 : Int) <= cur)) (PreH17 : (cur <= cap_pre)) (PreH18 : (SplitProgress (sublist ((0 : Int)) (i) (l)) cap_pre cnt cur)) ,
  TT && emp 
|--
  “ ((1 = 1) -> (SplitFeasible l m_pre cap_pre)) ”
  &&  emp
)

noncomputable def check_return_wit_2_split_goal_1 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : (cnt <= m_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : ((0 : Int) <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH11 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= cnt)) (PreH15 : (cnt <= (i + 1))) (PreH16 : ((0 : Int) <= cur)) (PreH17 : (cur <= cap_pre)) (PreH18 : (SplitProgress (sublist ((0 : Int)) (i) (l)) cap_pre cnt cur)) ,
  ((1 = 1) -> (SplitFeasible l m_pre cap_pre))

noncomputable def check_return_wit_3 : Prop :=
  (
forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : ((Znth i l (0 : Int)) > cap_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : ((0 : Int) <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH11 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= cnt)) (PreH15 : (cnt <= (i + 1))) (PreH16 : ((0 : Int) <= cur)) (PreH17 : (cur <= cap_pre)) (PreH18 : (SplitProgress (sublist ((0 : Int)) (i) (l)) cap_pre cnt cur)) ,
  (intArray.full arr_pre n_pre l)
|--
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 1) ” &&
  “ (((0 : Int) = 1) -> (SplitFeasible l m_pre cap_pre)) ” &&
  “ (((0 : Int) = (0 : Int)) -> (SplitInfeasible l m_pre cap_pre)) ”
  &&  (intArray.full arr_pre n_pre l)
) \/
(
forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : ((Znth i l (0 : Int)) > cap_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : ((0 : Int) <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH11 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= cnt)) (PreH15 : (cnt <= (i + 1))) (PreH16 : ((0 : Int) <= cur)) (PreH17 : (cur <= cap_pre)) (PreH18 : (SplitProgress (sublist ((0 : Int)) (i) (l)) cap_pre cnt cur)) ,
  TT && emp 
|--
  “ (((0 : Int) = (0 : Int)) -> (SplitInfeasible l m_pre cap_pre)) ”
  &&  emp
)

noncomputable def check_return_wit_3_split_goal_1 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : ((Znth i l (0 : Int)) > cap_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= n_pre)) (PreH7 : ((0 : Int) <= cap_pre)) (PreH8 : (cap_pre <= 1000000000)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH11 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (1 <= cnt)) (PreH15 : (cnt <= (i + 1))) (PreH16 : ((0 : Int) <= cur)) (PreH17 : (cur <= cap_pre)) (PreH18 : (SplitProgress (sublist ((0 : Int)) (i) (l)) cap_pre cnt cur)) ,
  (((0 : Int) = (0 : Int)) -> (SplitInfeasible l m_pre cap_pre))

noncomputable def check_partial_solve_wit_1 : Prop :=
  forall (cap_pre : Int) (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (cur : Int) (cnt : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((0 : Int) <= cap_pre)) (PreH7 : (cap_pre <= 1000000000)) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH10 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= cnt)) (PreH14 : (cnt <= (i + 1))) (PreH15 : ((0 : Int) <= cur)) (PreH16 : (cur <= cap_pre)) (PreH17 : (SplitProgress (sublist ((0 : Int)) (i) (l)) cap_pre cnt cur)) ,
  (intArray.full arr_pre n_pre l)
|--
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= n_pre) ” &&
  “ ((0 : Int) <= cap_pre) ” &&
  “ (cap_pre <= 1000000000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GT.gt (α := Int)) (100000000)) l) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= cnt) ” &&
  “ (cnt <= (i + 1)) ” &&
  “ ((0 : Int) <= cur) ” &&
  “ (cur <= cap_pre) ” &&
  “ (SplitProgress (sublist ((0 : Int)) (i) (l)) cap_pre cnt cur) ”
  &&  (((arr_pre + (i * sizeof(INT)))) # Int |-> ((Znth i l (0 : Int))))
  ** (intArray.missing_i arr_pre i (0 : Int) n_pre l)

noncomputable def splitArrayLargestSum_safety_wit_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= n_pre)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH7 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH8 : ((sum (l)) <= 1000000000)) (PreH9 : (MinimizedMaxSegmentSum l m_pre ans)) (PreH10 : ((0 : Int) <= ans)) (PreH11 : (ans <= 1000000000)) ,
  ((( &( "left" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def splitArrayLargestSum_safety_wit_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= n_pre)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH7 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH8 : ((sum (l)) <= 1000000000)) (PreH9 : (MinimizedMaxSegmentSum l m_pre ans)) (PreH10 : ((0 : Int) <= ans)) (PreH11 : (ans <= 1000000000)) ,
  ((( &( "right" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (1000000000 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1000000000) ”

noncomputable def splitArrayLargestSum_safety_wit_3 : Prop :=
  (
forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (PreH1 : (left < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH8 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (right <= 1000000000)) (PreH11 : (left <= right)) (PreH12 : (left <= res)) (PreH13 : (res <= right)) (PreH14 : (MinimizedMaxSegmentSum l m_pre res)) ,
  ((( &( "mid" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ ((left + (Z.quot (right - left) 2)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left + (Z.quot (right - left) 2))) ”
) \/
(
forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (PreH1 : (left < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH8 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (right <= 1000000000)) (PreH11 : (left <= right)) (PreH12 : (left <= res)) (PreH13 : (res <= right)) (PreH14 : (MinimizedMaxSegmentSum l m_pre res)) ,
  ((( &( "mid" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ ((left + (Z.quot (right - left) 2)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left + (Z.quot (right - left) 2))) ”
)

noncomputable def splitArrayLargestSum_safety_wit_3_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (PreH1 : (left < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH8 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (right <= 1000000000)) (PreH11 : (left <= right)) (PreH12 : (left <= res)) (PreH13 : (res <= right)) (PreH14 : (MinimizedMaxSegmentSum l m_pre res)) ,
  ((( &( "mid" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ ((left + (Z.quot (right - left) 2)) <= INT_MAX) ”

noncomputable def splitArrayLargestSum_safety_wit_3_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (PreH1 : (left < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH8 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (right <= 1000000000)) (PreH11 : (left <= right)) (PreH12 : (left <= res)) (PreH13 : (res <= right)) (PreH14 : (MinimizedMaxSegmentSum l m_pre res)) ,
  ((( &( "mid" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ ((INT_MIN) <= (left + (Z.quot (right - left) 2))) ”

noncomputable def splitArrayLargestSum_safety_wit_4 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (PreH1 : (left < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH8 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (right <= 1000000000)) (PreH11 : (left <= right)) (PreH12 : (left <= res)) (PreH13 : (res <= right)) (PreH14 : (MinimizedMaxSegmentSum l m_pre res)) ,
  ((( &( "mid" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ (((right - left) ≠ (INT_MIN)) ∨ (2 ≠ (-1))) ” &&
  “ (2 ≠ (0 : Int)) ”

noncomputable def splitArrayLargestSum_safety_wit_5 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (PreH1 : (left < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH8 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (right <= 1000000000)) (PreH11 : (left <= right)) (PreH12 : (left <= res)) (PreH13 : (res <= right)) (PreH14 : (MinimizedMaxSegmentSum l m_pre res)) ,
  ((( &( "mid" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ ((right - left) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (right - left)) ”

noncomputable def splitArrayLargestSum_safety_wit_6 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (PreH1 : (left < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH8 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (right <= 1000000000)) (PreH11 : (left <= right)) (PreH12 : (left <= res)) (PreH13 : (res <= right)) (PreH14 : (MinimizedMaxSegmentSum l m_pre res)) ,
  ((( &( "mid" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def splitArrayLargestSum_safety_wit_7 : Prop :=
  (
forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval = 1) -> (SplitFeasible l m_pre (left + (Z.quot (right - left) 2))))) (PreH4 : ((retval = (0 : Int)) -> (SplitInfeasible l m_pre (left + (Z.quot (right - left) 2))))) (PreH5 : (left < right)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH12 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH13 : ((0 : Int) <= left)) (PreH14 : (right <= 1000000000)) (PreH15 : (left <= right)) (PreH16 : (left <= res)) (PreH17 : (res <= right)) (PreH18 : (MinimizedMaxSegmentSum l m_pre res)) (PreH19 : (retval = (0 : Int))) ,
  (intArray.full arr_pre n_pre l)
  ** ((( &( "ok" ) )) # Int |-> (retval))
  ** ((( &( "mid" ) )) # Int |-> ((left + (Z.quot (right - left) 2))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ (((left + (Z.quot (right - left) 2)) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((left + (Z.quot (right - left) 2)) + 1)) ”
) \/
(
forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval = 1) -> (SplitFeasible l m_pre (left + (Z.quot (right - left) 2))))) (PreH4 : ((retval = (0 : Int)) -> (SplitInfeasible l m_pre (left + (Z.quot (right - left) 2))))) (PreH5 : (left < right)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH12 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH13 : ((0 : Int) <= left)) (PreH14 : (right <= 1000000000)) (PreH15 : (left <= right)) (PreH16 : (left <= res)) (PreH17 : (res <= right)) (PreH18 : (MinimizedMaxSegmentSum l m_pre res)) (PreH19 : (retval = (0 : Int))) ,
  (intArray.full arr_pre n_pre l)
  ** ((( &( "ok" ) )) # Int |-> (retval))
  ** ((( &( "mid" ) )) # Int |-> ((left + (Z.quot (right - left) 2))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ (((left + (Z.quot (right - left) 2)) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((left + (Z.quot (right - left) 2)) + 1)) ”
)

noncomputable def splitArrayLargestSum_safety_wit_7_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval = 1) -> (SplitFeasible l m_pre (left + (Z.quot (right - left) 2))))) (PreH4 : ((retval = (0 : Int)) -> (SplitInfeasible l m_pre (left + (Z.quot (right - left) 2))))) (PreH5 : (left < right)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH12 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH13 : ((0 : Int) <= left)) (PreH14 : (right <= 1000000000)) (PreH15 : (left <= right)) (PreH16 : (left <= res)) (PreH17 : (res <= right)) (PreH18 : (MinimizedMaxSegmentSum l m_pre res)) (PreH19 : (retval = (0 : Int))) ,
  (intArray.full arr_pre n_pre l)
  ** ((( &( "ok" ) )) # Int |-> (retval))
  ** ((( &( "mid" ) )) # Int |-> ((left + (Z.quot (right - left) 2))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ (((left + (Z.quot (right - left) 2)) + 1) <= INT_MAX) ”

noncomputable def splitArrayLargestSum_safety_wit_7_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval = 1) -> (SplitFeasible l m_pre (left + (Z.quot (right - left) 2))))) (PreH4 : ((retval = (0 : Int)) -> (SplitInfeasible l m_pre (left + (Z.quot (right - left) 2))))) (PreH5 : (left < right)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH12 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH13 : ((0 : Int) <= left)) (PreH14 : (right <= 1000000000)) (PreH15 : (left <= right)) (PreH16 : (left <= res)) (PreH17 : (res <= right)) (PreH18 : (MinimizedMaxSegmentSum l m_pre res)) (PreH19 : (retval = (0 : Int))) ,
  (intArray.full arr_pre n_pre l)
  ** ((( &( "ok" ) )) # Int |-> (retval))
  ** ((( &( "mid" ) )) # Int |-> ((left + (Z.quot (right - left) 2))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ ((INT_MIN) <= ((left + (Z.quot (right - left) 2)) + 1)) ”

noncomputable def splitArrayLargestSum_safety_wit_8 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval = 1) -> (SplitFeasible l m_pre (left + (Z.quot (right - left) 2))))) (PreH4 : ((retval = (0 : Int)) -> (SplitInfeasible l m_pre (left + (Z.quot (right - left) 2))))) (PreH5 : (left < right)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH12 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH13 : ((0 : Int) <= left)) (PreH14 : (right <= 1000000000)) (PreH15 : (left <= right)) (PreH16 : (left <= res)) (PreH17 : (res <= right)) (PreH18 : (MinimizedMaxSegmentSum l m_pre res)) (PreH19 : (retval = (0 : Int))) ,
  (intArray.full arr_pre n_pre l)
  ** ((( &( "ok" ) )) # Int |-> (retval))
  ** ((( &( "mid" ) )) # Int |-> ((left + (Z.quot (right - left) 2))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def splitArrayLargestSum_entail_wit_1 : Prop :=
  (
forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (ans : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= n_pre)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH7 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH8 : ((sum (l)) <= 1000000000)) (PreH9 : (MinimizedMaxSegmentSum l m_pre ans)) (PreH10 : ((0 : Int) <= ans)) (PreH11 : (ans <= 1000000000)) ,
  (intArray.full arr_pre n_pre l)
|--
  EX res : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= n_pre) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GT.gt (α := Int)) (100000000)) l) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ (1000000000 <= 1000000000) ” &&
  “ ((0 : Int) <= 1000000000) ” &&
  “ ((0 : Int) <= res) ” &&
  “ (res <= 1000000000) ” &&
  “ (MinimizedMaxSegmentSum l m_pre res) ”
  &&  (intArray.full arr_pre n_pre l)
) \/
(
forall (m_pre : Int) (n_pre : Int) (l : (List Int)) (ans : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= n_pre)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH7 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH8 : ((sum (l)) <= 1000000000)) (PreH9 : (MinimizedMaxSegmentSum l m_pre ans)) (PreH10 : ((0 : Int) <= ans)) (PreH11 : (ans <= 1000000000)) ,
  TT && emp 
|--
  EX res : Int,
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ (1000000000 <= 1000000000) ” &&
  “ ((0 : Int) <= 1000000000) ” &&
  “ ((0 : Int) <= res) ” &&
  “ (res <= 1000000000) ” &&
  “ (MinimizedMaxSegmentSum l m_pre res) ”
  &&  emp
)

noncomputable def splitArrayLargestSum_entail_wit_2_1 : Prop :=
  (
forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res_2 : Int) (right : Int) (left : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval = 1) -> (SplitFeasible l m_pre (left + (Z.quot (right - left) 2))))) (PreH4 : ((retval = (0 : Int)) -> (SplitInfeasible l m_pre (left + (Z.quot (right - left) 2))))) (PreH5 : (left < right)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH12 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH13 : ((0 : Int) <= left)) (PreH14 : (right <= 1000000000)) (PreH15 : (left <= right)) (PreH16 : (left <= res_2)) (PreH17 : (res_2 <= right)) (PreH18 : (MinimizedMaxSegmentSum l m_pre res_2)) (PreH19 : (retval ≠ (0 : Int))) ,
  (intArray.full arr_pre n_pre l)
|--
  EX res : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= n_pre) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GT.gt (α := Int)) (100000000)) l) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + (Z.quot (right - left) 2)) <= 1000000000) ” &&
  “ (left <= (left + (Z.quot (right - left) 2))) ” &&
  “ (left <= res) ” &&
  “ (res <= (left + (Z.quot (right - left) 2))) ” &&
  “ (MinimizedMaxSegmentSum l m_pre res) ”
  &&  (intArray.full arr_pre n_pre l)
) \/
(
forall (m_pre : Int) (n_pre : Int) (l : (List Int)) (res_2 : Int) (right : Int) (left : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval = 1) -> (SplitFeasible l m_pre (left + (Z.quot (right - left) 2))))) (PreH4 : ((retval = (0 : Int)) -> (SplitInfeasible l m_pre (left + (Z.quot (right - left) 2))))) (PreH5 : (left < right)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH12 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH13 : ((0 : Int) <= left)) (PreH14 : (right <= 1000000000)) (PreH15 : (left <= right)) (PreH16 : (left <= res_2)) (PreH17 : (res_2 <= right)) (PreH18 : (MinimizedMaxSegmentSum l m_pre res_2)) (PreH19 : (retval ≠ (0 : Int))) ,
  TT && emp 
|--
  EX res : Int,
  “ ((left + (Z.quot (right - left) 2)) <= 1000000000) ” &&
  “ (left <= (left + (Z.quot (right - left) 2))) ” &&
  “ (left <= res) ” &&
  “ (res <= (left + (Z.quot (right - left) 2))) ” &&
  “ (MinimizedMaxSegmentSum l m_pre res) ”
  &&  emp
)

noncomputable def splitArrayLargestSum_entail_wit_2_2 : Prop :=
  (
forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res_2 : Int) (right : Int) (left : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval = 1) -> (SplitFeasible l m_pre (left + (Z.quot (right - left) 2))))) (PreH4 : ((retval = (0 : Int)) -> (SplitInfeasible l m_pre (left + (Z.quot (right - left) 2))))) (PreH5 : (left < right)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH12 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH13 : ((0 : Int) <= left)) (PreH14 : (right <= 1000000000)) (PreH15 : (left <= right)) (PreH16 : (left <= res_2)) (PreH17 : (res_2 <= right)) (PreH18 : (MinimizedMaxSegmentSum l m_pre res_2)) (PreH19 : (retval = (0 : Int))) ,
  (intArray.full arr_pre n_pre l)
|--
  EX res : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= n_pre) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GT.gt (α := Int)) (100000000)) l) ” &&
  “ ((0 : Int) <= ((left + (Z.quot (right - left) 2)) + 1)) ” &&
  “ (right <= 1000000000) ” &&
  “ (((left + (Z.quot (right - left) 2)) + 1) <= right) ” &&
  “ (((left + (Z.quot (right - left) 2)) + 1) <= res) ” &&
  “ (res <= right) ” &&
  “ (MinimizedMaxSegmentSum l m_pre res) ”
  &&  (intArray.full arr_pre n_pre l)
) \/
(
forall (m_pre : Int) (n_pre : Int) (l : (List Int)) (res_2 : Int) (right : Int) (left : Int) (retval : Int) (PreH1 : ((0 : Int) <= retval)) (PreH2 : (retval <= 1)) (PreH3 : ((retval = 1) -> (SplitFeasible l m_pre (left + (Z.quot (right - left) 2))))) (PreH4 : ((retval = (0 : Int)) -> (SplitInfeasible l m_pre (left + (Z.quot (right - left) 2))))) (PreH5 : (left < right)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH12 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH13 : ((0 : Int) <= left)) (PreH14 : (right <= 1000000000)) (PreH15 : (left <= right)) (PreH16 : (left <= res_2)) (PreH17 : (res_2 <= right)) (PreH18 : (MinimizedMaxSegmentSum l m_pre res_2)) (PreH19 : (retval = (0 : Int))) ,
  TT && emp 
|--
  EX res : Int,
  “ ((0 : Int) <= ((left + (Z.quot (right - left) 2)) + 1)) ” &&
  “ (((left + (Z.quot (right - left) 2)) + 1) <= right) ” &&
  “ (((left + (Z.quot (right - left) 2)) + 1) <= res) ” &&
  “ (res <= right) ” &&
  “ (MinimizedMaxSegmentSum l m_pre res) ”
  &&  emp
)

noncomputable def splitArrayLargestSum_return_wit_1 : Prop :=
  (
forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (PreH1 : (left >= right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH8 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (right <= 1000000000)) (PreH11 : (left <= right)) (PreH12 : (left <= res)) (PreH13 : (res <= right)) (PreH14 : (MinimizedMaxSegmentSum l m_pre res)) ,
  (intArray.full arr_pre n_pre l)
|--
  “ (MinimizedMaxSegmentSum l m_pre left) ”
  &&  (intArray.full arr_pre n_pre l)
) \/
(
forall (m_pre : Int) (n_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (PreH1 : (left >= right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH8 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (right <= 1000000000)) (PreH11 : (left <= right)) (PreH12 : (left <= res)) (PreH13 : (res <= right)) (PreH14 : (MinimizedMaxSegmentSum l m_pre res)) ,
  TT && emp 
|--
  “ (MinimizedMaxSegmentSum l m_pre left) ”
  &&  emp
)

noncomputable def splitArrayLargestSum_return_wit_1_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (PreH1 : (left >= right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH8 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (right <= 1000000000)) (PreH11 : (left <= right)) (PreH12 : (left <= res)) (PreH13 : (res <= right)) (PreH14 : (MinimizedMaxSegmentSum l m_pre res)) ,
  (MinimizedMaxSegmentSum l m_pre left)

noncomputable def splitArrayLargestSum_partial_solve_wit_1_pure : Prop :=
  (
forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (PreH1 : (left < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH8 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (right <= 1000000000)) (PreH11 : (left <= right)) (PreH12 : (left <= res)) (PreH13 : (res <= right)) (PreH14 : (MinimizedMaxSegmentSum l m_pre res)) ,
  ((( &( "ok" ) )) # Int |->_)
  ** ((( &( "mid" ) )) # Int |-> ((left + (Z.quot (right - left) 2))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= n_pre) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GT.gt (α := Int)) (100000000)) l) ” &&
  “ ((left + (Z.quot (right - left) 2)) <= 1000000000) ” &&
  “ ((0 : Int) <= (left + (Z.quot (right - left) 2))) ”
) \/
(
forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (PreH1 : (right <= INT_MAX)) (PreH2 : (left <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((left + (Z.quot (right - left) 2)) <= INT_MAX)) (PreH6 : (right >= INT_MIN)) (PreH7 : (left >= INT_MIN)) (PreH8 : (m_pre >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((left + (Z.quot (right - left) 2)) >= INT_MIN)) (PreH11 : (left < right)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= n_pre)) (PreH16 : ((Zlength (l)) = n_pre)) (PreH17 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH18 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH19 : ((0 : Int) <= left)) (PreH20 : (right <= 1000000000)) (PreH21 : (left <= right)) (PreH22 : (left <= res)) (PreH23 : (res <= right)) (PreH24 : (MinimizedMaxSegmentSum l m_pre res)) ,
  ((( &( "ok" ) )) # Int |->_)
  ** ((( &( "mid" ) )) # Int |-> ((left + (Z.quot (right - left) 2))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ ((0 : Int) <= (left + (Z.quot (right - left) 2))) ” &&
  “ ((left + (Z.quot (right - left) 2)) <= 1000000000) ”
)

noncomputable def splitArrayLargestSum_partial_solve_wit_1_pure_split_goal_1 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (PreH1 : (right <= INT_MAX)) (PreH2 : (left <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((left + (Z.quot (right - left) 2)) <= INT_MAX)) (PreH6 : (right >= INT_MIN)) (PreH7 : (left >= INT_MIN)) (PreH8 : (m_pre >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((left + (Z.quot (right - left) 2)) >= INT_MIN)) (PreH11 : (left < right)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= n_pre)) (PreH16 : ((Zlength (l)) = n_pre)) (PreH17 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH18 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH19 : ((0 : Int) <= left)) (PreH20 : (right <= 1000000000)) (PreH21 : (left <= right)) (PreH22 : (left <= res)) (PreH23 : (res <= right)) (PreH24 : (MinimizedMaxSegmentSum l m_pre res)) ,
  ((( &( "ok" ) )) # Int |->_)
  ** ((( &( "mid" ) )) # Int |-> ((left + (Z.quot (right - left) 2))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ ((0 : Int) <= (left + (Z.quot (right - left) 2))) ”

noncomputable def splitArrayLargestSum_partial_solve_wit_1_pure_split_goal_2 : Prop :=
  forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (PreH1 : (right <= INT_MAX)) (PreH2 : (left <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((left + (Z.quot (right - left) 2)) <= INT_MAX)) (PreH6 : (right >= INT_MIN)) (PreH7 : (left >= INT_MIN)) (PreH8 : (m_pre >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((left + (Z.quot (right - left) 2)) >= INT_MIN)) (PreH11 : (left < right)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= n_pre)) (PreH16 : ((Zlength (l)) = n_pre)) (PreH17 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH18 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH19 : ((0 : Int) <= left)) (PreH20 : (right <= 1000000000)) (PreH21 : (left <= right)) (PreH22 : (left <= res)) (PreH23 : (res <= right)) (PreH24 : (MinimizedMaxSegmentSum l m_pre res)) ,
  ((( &( "ok" ) )) # Int |->_)
  ** ((( &( "mid" ) )) # Int |-> ((left + (Z.quot (right - left) 2))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
|--
  “ ((left + (Z.quot (right - left) 2)) <= 1000000000) ”

noncomputable def splitArrayLargestSum_partial_solve_wit_1_aux : Prop :=
  forall (m_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (res : Int) (right : Int) (left : Int) (PreH1 : (left < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= n_pre)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH8 : (Forall ((GT.gt (α := Int)) (100000000)) l)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (right <= 1000000000)) (PreH11 : (left <= right)) (PreH12 : (left <= res)) (PreH13 : (res <= right)) (PreH14 : (MinimizedMaxSegmentSum l m_pre res)) ,
  (intArray.full arr_pre n_pre l)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= n_pre) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GT.gt (α := Int)) (100000000)) l) ” &&
  “ ((left + (Z.quot (right - left) 2)) <= 1000000000) ” &&
  “ ((0 : Int) <= (left + (Z.quot (right - left) 2))) ” &&
  “ (left < right) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= m_pre) ” &&
  “ (m_pre <= n_pre) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GT.gt (α := Int)) (100000000)) l) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (right <= 1000000000) ” &&
  “ (left <= right) ” &&
  “ (left <= res) ” &&
  “ (res <= right) ” &&
  “ (MinimizedMaxSegmentSum l m_pre res) ”
  &&  (intArray.full arr_pre n_pre l)

noncomputable def splitArrayLargestSum_partial_solve_wit_1 : Prop := splitArrayLargestSum_partial_solve_wit_1_pure -> splitArrayLargestSum_partial_solve_wit_1_aux


structure VC_Correct : Type where
  proof_of_check_safety_wit_1 : check_safety_wit_1
  proof_of_check_safety_wit_2 : check_safety_wit_2
  proof_of_check_safety_wit_3 : check_safety_wit_3
  proof_of_check_safety_wit_4 : check_safety_wit_4
  proof_of_check_safety_wit_5 : check_safety_wit_5
  proof_of_check_safety_wit_6 : check_safety_wit_6
  proof_of_check_safety_wit_7 : check_safety_wit_7
  proof_of_check_safety_wit_8 : check_safety_wit_8
  proof_of_check_safety_wit_9 : check_safety_wit_9
  proof_of_check_safety_wit_10 : check_safety_wit_10
  proof_of_check_safety_wit_11 : check_safety_wit_11
  proof_of_check_safety_wit_12 : check_safety_wit_12
  proof_of_check_partial_solve_wit_1 : check_partial_solve_wit_1
  proof_of_splitArrayLargestSum_safety_wit_1 : splitArrayLargestSum_safety_wit_1
  proof_of_splitArrayLargestSum_safety_wit_2 : splitArrayLargestSum_safety_wit_2
  proof_of_splitArrayLargestSum_safety_wit_4 : splitArrayLargestSum_safety_wit_4
  proof_of_splitArrayLargestSum_safety_wit_5 : splitArrayLargestSum_safety_wit_5
  proof_of_splitArrayLargestSum_safety_wit_6 : splitArrayLargestSum_safety_wit_6
  proof_of_splitArrayLargestSum_safety_wit_8 : splitArrayLargestSum_safety_wit_8
  proof_of_splitArrayLargestSum_partial_solve_wit_1 : splitArrayLargestSum_partial_solve_wit_1
  proof_of_check_entail_wit_1 : check_entail_wit_1
  proof_of_check_entail_wit_2_1 : check_entail_wit_2_1
  proof_of_check_entail_wit_2_2 : check_entail_wit_2_2
  proof_of_check_return_wit_1 : check_return_wit_1
  proof_of_check_return_wit_2 : check_return_wit_2
  proof_of_check_return_wit_3 : check_return_wit_3
  proof_of_splitArrayLargestSum_safety_wit_3 : splitArrayLargestSum_safety_wit_3
  proof_of_splitArrayLargestSum_safety_wit_7 : splitArrayLargestSum_safety_wit_7
  proof_of_splitArrayLargestSum_entail_wit_1 : splitArrayLargestSum_entail_wit_1
  proof_of_splitArrayLargestSum_entail_wit_2_1 : splitArrayLargestSum_entail_wit_2_1
  proof_of_splitArrayLargestSum_entail_wit_2_2 : splitArrayLargestSum_entail_wit_2_2
  proof_of_splitArrayLargestSum_return_wit_1 : splitArrayLargestSum_return_wit_1
  proof_of_splitArrayLargestSum_partial_solve_wit_1_pure : splitArrayLargestSum_partial_solve_wit_1_pure

end SimpleC.EE.LLM_bench.Algorithms.split_array_largest_sum.split_array_largest_sum_goal
