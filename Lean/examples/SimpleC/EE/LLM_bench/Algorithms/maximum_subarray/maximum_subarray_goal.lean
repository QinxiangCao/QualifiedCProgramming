import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.maximum_subarray.maximum_subarray_lib
open SimpleC.EE.LLM_bench.Algorithms.maximum_subarray.maximum_subarray_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.maximum_subarray.maximum_subarray_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance maximum_subarray_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def max_return_wit_1 : Prop :=
  (
forall (a_pre : Int) (b_pre : Int) (PreH1 : (a_pre > b_pre)) ,
  TT && emp 
|--
  “ (a_pre = (max_Z (a_pre) (b_pre))) ”
  &&  emp
) \/
(
forall (a_pre : Int) (b_pre : Int) (PreH1 : (a_pre > b_pre)) ,
  TT && emp 
|--
  “ (a_pre = (max_Z (a_pre) (b_pre))) ”
  &&  emp
)

noncomputable def max_return_wit_1_split_goal_1 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (PreH1 : (a_pre > b_pre)) ,
  (a_pre = (max_Z (a_pre) (b_pre)))

noncomputable def max_return_wit_2 : Prop :=
  (
forall (a_pre : Int) (b_pre : Int) (PreH1 : (a_pre <= b_pre)) ,
  TT && emp 
|--
  “ (b_pre = (max_Z (a_pre) (b_pre))) ”
  &&  emp
) \/
(
forall (a_pre : Int) (b_pre : Int) (PreH1 : (a_pre <= b_pre)) ,
  TT && emp 
|--
  “ (b_pre = (max_Z (a_pre) (b_pre))) ”
  &&  emp
)

noncomputable def max_return_wit_2_split_goal_1 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (PreH1 : (a_pre <= b_pre)) ,
  (b_pre = (max_Z (a_pre) (b_pre)))

noncomputable def max_sub_array_safety_wit_1 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH5 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def max_sub_array_safety_wit_2 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (PreH1 : (n_pre = (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full arr_pre n_pre l)
|--
  “ False ”

noncomputable def max_sub_array_safety_wit_3 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (PreH1 : (n_pre ≠ (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "cur" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def max_sub_array_safety_wit_4 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (PreH1 : (n_pre ≠ (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "res" ) )) # Int |->_)
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "cur" ) )) # Int |-> ((Znth (0 : Int) l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def max_sub_array_safety_wit_5 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (PreH1 : (n_pre ≠ (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "i" ) )) # Int |->_)
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "res" ) )) # Int |-> ((Znth (0 : Int) l (0 : Int))))
  ** ((( &( "cur" ) )) # Int |-> ((Znth (0 : Int) l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def max_sub_array_safety_wit_6 : Prop :=
  (
forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (res : Int) (cur : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (MaxSuffixSumPrefix l i cur)) (PreH12 : (MaxSubarraySumPrefix l i res)) (PreH13 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full arr_pre n_pre l)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cur" ) )) # Int |-> (cur))
  ** ((( &( "res" ) )) # Int |-> (res))
|--
  “ ((cur + (Znth i l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (cur + (Znth i l (0 : Int)))) ”
) \/
(
forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (res : Int) (cur : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (MaxSuffixSumPrefix l i cur)) (PreH12 : (MaxSubarraySumPrefix l i res)) (PreH13 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full arr_pre n_pre l)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cur" ) )) # Int |-> (cur))
  ** ((( &( "res" ) )) # Int |-> (res))
|--
  “ ((cur + (Znth i l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (cur + (Znth i l (0 : Int)))) ”
)

noncomputable def max_sub_array_safety_wit_6_split_goal_1 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (res : Int) (cur : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (MaxSuffixSumPrefix l i cur)) (PreH12 : (MaxSubarraySumPrefix l i res)) (PreH13 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full arr_pre n_pre l)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cur" ) )) # Int |-> (cur))
  ** ((( &( "res" ) )) # Int |-> (res))
|--
  “ ((cur + (Znth i l (0 : Int))) <= INT_MAX) ”

noncomputable def max_sub_array_safety_wit_6_split_goal_2 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (res : Int) (cur : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (MaxSuffixSumPrefix l i cur)) (PreH12 : (MaxSubarraySumPrefix l i res)) (PreH13 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full arr_pre n_pre l)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cur" ) )) # Int |-> (cur))
  ** ((( &( "res" ) )) # Int |-> (res))
|--
  “ ((INT_MIN) <= (cur + (Znth i l (0 : Int)))) ”

noncomputable def max_sub_array_safety_wit_7 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (res : Int) (cur : Int) (i : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (max_Z (res) (retval)))) (PreH2 : (retval = (max_Z ((Znth i l (0 : Int))) ((cur + (Znth i l (0 : Int))))))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((-10000) <= cur)) (PreH10 : (cur <= 1000000000)) (PreH11 : ((-10000) <= res)) (PreH12 : (res <= 1000000000)) (PreH13 : (MaxSuffixSumPrefix l i cur)) (PreH14 : (MaxSubarraySumPrefix l i res)) (PreH15 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH16 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full arr_pre n_pre l)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cur" ) )) # Int |-> (retval))
  ** ((( &( "res" ) )) # Int |-> (retval_2))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def max_sub_array_entail_wit_1 : Prop :=
  (
forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (PreH1 : (n_pre ≠ (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full arr_pre n_pre l)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= n_pre) ” &&
  “ ((-10000) <= (Znth (0 : Int) l (0 : Int))) ” &&
  “ ((Znth (0 : Int) l (0 : Int)) <= 1000000000) ” &&
  “ ((-10000) <= (Znth (0 : Int) l (0 : Int))) ” &&
  “ ((Znth (0 : Int) l (0 : Int)) <= 1000000000) ” &&
  “ (MaxSuffixSumPrefix l 1 (Znth (0 : Int) l (0 : Int))) ” &&
  “ (MaxSubarraySumPrefix l 1 (Znth (0 : Int) l (0 : Int))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full arr_pre n_pre l)
) \/
(
forall (l : (List Int)) (n_pre : Int) (PreH1 : (n_pre ≠ (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ (MaxSubarraySumPrefix l 1 (Znth (0 : Int) l (0 : Int))) ” &&
  “ (MaxSuffixSumPrefix l 1 (Znth (0 : Int) l (0 : Int))) ” &&
  “ ((Znth (0 : Int) l (0 : Int)) <= 1000000000) ” &&
  “ ((-10000) <= (Znth (0 : Int) l (0 : Int))) ” &&
  “ ((Znth (0 : Int) l (0 : Int)) <= 1000000000) ” &&
  “ ((-10000) <= (Znth (0 : Int) l (0 : Int))) ”
  &&  emp
)

noncomputable def max_sub_array_entail_wit_1_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (PreH1 : (n_pre ≠ (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (MaxSubarraySumPrefix l 1 (Znth (0 : Int) l (0 : Int)))

noncomputable def max_sub_array_entail_wit_1_split_goal_2 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (PreH1 : (n_pre ≠ (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (MaxSuffixSumPrefix l 1 (Znth (0 : Int) l (0 : Int)))

noncomputable def max_sub_array_entail_wit_1_split_goal_3 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (PreH1 : (n_pre ≠ (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((Znth (0 : Int) l (0 : Int)) <= 1000000000)

noncomputable def max_sub_array_entail_wit_1_split_goal_4 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (PreH1 : (n_pre ≠ (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((-10000) <= (Znth (0 : Int) l (0 : Int)))

noncomputable def max_sub_array_entail_wit_1_split_goal_5 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (PreH1 : (n_pre ≠ (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((Znth (0 : Int) l (0 : Int)) <= 1000000000)

noncomputable def max_sub_array_entail_wit_1_split_goal_6 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (PreH1 : (n_pre ≠ (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((-10000) <= (Znth (0 : Int) l (0 : Int)))

noncomputable def max_sub_array_entail_wit_2 : Prop :=
  (
forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (res : Int) (cur : Int) (i : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (max_Z (res) (retval)))) (PreH2 : (retval = (max_Z ((Znth i l (0 : Int))) ((cur + (Znth i l (0 : Int))))))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((-10000) <= cur)) (PreH10 : (cur <= 1000000000)) (PreH11 : ((-10000) <= res)) (PreH12 : (res <= 1000000000)) (PreH13 : (MaxSuffixSumPrefix l i cur)) (PreH14 : (MaxSubarraySumPrefix l i res)) (PreH15 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH16 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full arr_pre n_pre l)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((-10000) <= retval) ” &&
  “ (retval <= 1000000000) ” &&
  “ ((-10000) <= retval_2) ” &&
  “ (retval_2 <= 1000000000) ” &&
  “ (MaxSuffixSumPrefix l (i + 1) retval) ” &&
  “ (MaxSubarraySumPrefix l (i + 1) retval_2) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full arr_pre n_pre l)
) \/
(
forall (l : (List Int)) (n_pre : Int) (res : Int) (cur : Int) (i : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (max_Z (res) (retval)))) (PreH2 : (retval = (max_Z ((Znth i l (0 : Int))) ((cur + (Znth i l (0 : Int))))))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((-10000) <= cur)) (PreH10 : (cur <= 1000000000)) (PreH11 : ((-10000) <= res)) (PreH12 : (res <= 1000000000)) (PreH13 : (MaxSuffixSumPrefix l i cur)) (PreH14 : (MaxSubarraySumPrefix l i res)) (PreH15 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH16 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ (MaxSubarraySumPrefix l (i + 1) retval_2) ” &&
  “ (MaxSuffixSumPrefix l (i + 1) retval) ” &&
  “ (retval_2 <= 1000000000) ” &&
  “ ((-10000) <= retval_2) ” &&
  “ (retval <= 1000000000) ” &&
  “ ((-10000) <= retval) ”
  &&  emp
)

noncomputable def max_sub_array_entail_wit_2_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (res : Int) (cur : Int) (i : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (max_Z (res) (retval)))) (PreH2 : (retval = (max_Z ((Znth i l (0 : Int))) ((cur + (Znth i l (0 : Int))))))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((-10000) <= cur)) (PreH10 : (cur <= 1000000000)) (PreH11 : ((-10000) <= res)) (PreH12 : (res <= 1000000000)) (PreH13 : (MaxSuffixSumPrefix l i cur)) (PreH14 : (MaxSubarraySumPrefix l i res)) (PreH15 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH16 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (MaxSubarraySumPrefix l (i + 1) retval_2)

noncomputable def max_sub_array_entail_wit_2_split_goal_2 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (res : Int) (cur : Int) (i : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (max_Z (res) (retval)))) (PreH2 : (retval = (max_Z ((Znth i l (0 : Int))) ((cur + (Znth i l (0 : Int))))))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((-10000) <= cur)) (PreH10 : (cur <= 1000000000)) (PreH11 : ((-10000) <= res)) (PreH12 : (res <= 1000000000)) (PreH13 : (MaxSuffixSumPrefix l i cur)) (PreH14 : (MaxSubarraySumPrefix l i res)) (PreH15 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH16 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (MaxSuffixSumPrefix l (i + 1) retval)

noncomputable def max_sub_array_entail_wit_2_split_goal_3 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (res : Int) (cur : Int) (i : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (max_Z (res) (retval)))) (PreH2 : (retval = (max_Z ((Znth i l (0 : Int))) ((cur + (Znth i l (0 : Int))))))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((-10000) <= cur)) (PreH10 : (cur <= 1000000000)) (PreH11 : ((-10000) <= res)) (PreH12 : (res <= 1000000000)) (PreH13 : (MaxSuffixSumPrefix l i cur)) (PreH14 : (MaxSubarraySumPrefix l i res)) (PreH15 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH16 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (retval_2 <= 1000000000)

noncomputable def max_sub_array_entail_wit_2_split_goal_4 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (res : Int) (cur : Int) (i : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (max_Z (res) (retval)))) (PreH2 : (retval = (max_Z ((Znth i l (0 : Int))) ((cur + (Znth i l (0 : Int))))))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((-10000) <= cur)) (PreH10 : (cur <= 1000000000)) (PreH11 : ((-10000) <= res)) (PreH12 : (res <= 1000000000)) (PreH13 : (MaxSuffixSumPrefix l i cur)) (PreH14 : (MaxSubarraySumPrefix l i res)) (PreH15 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH16 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((-10000) <= retval_2)

noncomputable def max_sub_array_entail_wit_2_split_goal_5 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (res : Int) (cur : Int) (i : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (max_Z (res) (retval)))) (PreH2 : (retval = (max_Z ((Znth i l (0 : Int))) ((cur + (Znth i l (0 : Int))))))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((-10000) <= cur)) (PreH10 : (cur <= 1000000000)) (PreH11 : ((-10000) <= res)) (PreH12 : (res <= 1000000000)) (PreH13 : (MaxSuffixSumPrefix l i cur)) (PreH14 : (MaxSubarraySumPrefix l i res)) (PreH15 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH16 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (retval <= 1000000000)

noncomputable def max_sub_array_entail_wit_2_split_goal_6 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (res : Int) (cur : Int) (i : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (max_Z (res) (retval)))) (PreH2 : (retval = (max_Z ((Znth i l (0 : Int))) ((cur + (Znth i l (0 : Int))))))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((-10000) <= cur)) (PreH10 : (cur <= 1000000000)) (PreH11 : ((-10000) <= res)) (PreH12 : (res <= 1000000000)) (PreH13 : (MaxSuffixSumPrefix l i cur)) (PreH14 : (MaxSubarraySumPrefix l i res)) (PreH15 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH16 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((-10000) <= retval)

noncomputable def max_sub_array_return_wit_1 : Prop :=
  (
forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (res : Int) (cur : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (MaxSuffixSumPrefix l i cur)) (PreH12 : (MaxSubarraySumPrefix l i res)) (PreH13 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full arr_pre n_pre l)
|--
  “ (MaxSubarraySumPrefix l n_pre res) ”
  &&  (intArray.full arr_pre n_pre l)
) \/
(
forall (l : (List Int)) (n_pre : Int) (res : Int) (cur : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (MaxSuffixSumPrefix l i cur)) (PreH12 : (MaxSubarraySumPrefix l i res)) (PreH13 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ (MaxSubarraySumPrefix l n_pre res) ”
  &&  emp
)

noncomputable def max_sub_array_return_wit_1_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (res : Int) (cur : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (MaxSuffixSumPrefix l i cur)) (PreH12 : (MaxSubarraySumPrefix l i res)) (PreH13 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (MaxSubarraySumPrefix l n_pre res)

noncomputable def max_sub_array_partial_solve_wit_1 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (PreH1 : (n_pre ≠ (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full arr_pre n_pre l)
|--
  “ (n_pre ≠ (0 : Int)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (((arr_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((Znth (0 : Int) l (0 : Int))))
  ** (intArray.missing_i arr_pre (0 : Int) (0 : Int) n_pre l)

noncomputable def max_sub_array_partial_solve_wit_2 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (PreH1 : (n_pre ≠ (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full arr_pre n_pre l)
|--
  “ (n_pre ≠ (0 : Int)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (((arr_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((Znth (0 : Int) l (0 : Int))))
  ** (intArray.missing_i arr_pre (0 : Int) (0 : Int) n_pre l)

noncomputable def max_sub_array_partial_solve_wit_3 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (res : Int) (cur : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (MaxSuffixSumPrefix l i cur)) (PreH12 : (MaxSubarraySumPrefix l i res)) (PreH13 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full arr_pre n_pre l)
|--
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((-10000) <= cur) ” &&
  “ (cur <= 1000000000) ” &&
  “ ((-10000) <= res) ” &&
  “ (res <= 1000000000) ” &&
  “ (MaxSuffixSumPrefix l i cur) ” &&
  “ (MaxSubarraySumPrefix l i res) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (((arr_pre + (i * sizeof(INT)))) # Int |-> ((Znth i l (0 : Int))))
  ** (intArray.missing_i arr_pre i (0 : Int) n_pre l)

noncomputable def max_sub_array_partial_solve_wit_4 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (res : Int) (cur : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (MaxSuffixSumPrefix l i cur)) (PreH12 : (MaxSubarraySumPrefix l i res)) (PreH13 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full arr_pre n_pre l)
|--
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((-10000) <= cur) ” &&
  “ (cur <= 1000000000) ” &&
  “ ((-10000) <= res) ” &&
  “ (res <= 1000000000) ” &&
  “ (MaxSuffixSumPrefix l i cur) ” &&
  “ (MaxSubarraySumPrefix l i res) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (((arr_pre + (i * sizeof(INT)))) # Int |-> ((Znth i l (0 : Int))))
  ** (intArray.missing_i arr_pre i (0 : Int) n_pre l)

noncomputable def max_sub_array_partial_solve_wit_5 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (res : Int) (cur : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((-10000) <= cur)) (PreH8 : (cur <= 1000000000)) (PreH9 : ((-10000) <= res)) (PreH10 : (res <= 1000000000)) (PreH11 : (MaxSuffixSumPrefix l i cur)) (PreH12 : (MaxSubarraySumPrefix l i res)) (PreH13 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full arr_pre n_pre l)
|--
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((-10000) <= cur) ” &&
  “ (cur <= 1000000000) ” &&
  “ ((-10000) <= res) ” &&
  “ (res <= 1000000000) ” &&
  “ (MaxSuffixSumPrefix l i cur) ” &&
  “ (MaxSubarraySumPrefix l i res) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full arr_pre n_pre l)

noncomputable def max_sub_array_partial_solve_wit_6 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (res : Int) (cur : Int) (i : Int) (retval : Int) (PreH1 : (retval = (max_Z ((Znth i l (0 : Int))) ((cur + (Znth i l (0 : Int))))))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((-10000) <= cur)) (PreH9 : (cur <= 1000000000)) (PreH10 : ((-10000) <= res)) (PreH11 : (res <= 1000000000)) (PreH12 : (MaxSuffixSumPrefix l i cur)) (PreH13 : (MaxSubarraySumPrefix l i res)) (PreH14 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH15 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full arr_pre n_pre l)
|--
  “ (retval = (max_Z ((Znth i l (0 : Int))) ((cur + (Znth i l (0 : Int)))))) ” &&
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((-10000) <= cur) ” &&
  “ (cur <= 1000000000) ” &&
  “ ((-10000) <= res) ” &&
  “ (res <= 1000000000) ” &&
  “ (MaxSuffixSumPrefix l i cur) ” &&
  “ (MaxSubarraySumPrefix l i res) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ”
  &&  (intArray.full arr_pre n_pre l)


structure VC_Correct : Type where
  proof_of_max_sub_array_safety_wit_1 : max_sub_array_safety_wit_1
  proof_of_max_sub_array_safety_wit_2 : max_sub_array_safety_wit_2
  proof_of_max_sub_array_safety_wit_3 : max_sub_array_safety_wit_3
  proof_of_max_sub_array_safety_wit_4 : max_sub_array_safety_wit_4
  proof_of_max_sub_array_safety_wit_5 : max_sub_array_safety_wit_5
  proof_of_max_sub_array_safety_wit_7 : max_sub_array_safety_wit_7
  proof_of_max_sub_array_partial_solve_wit_1 : max_sub_array_partial_solve_wit_1
  proof_of_max_sub_array_partial_solve_wit_2 : max_sub_array_partial_solve_wit_2
  proof_of_max_sub_array_partial_solve_wit_3 : max_sub_array_partial_solve_wit_3
  proof_of_max_sub_array_partial_solve_wit_4 : max_sub_array_partial_solve_wit_4
  proof_of_max_sub_array_partial_solve_wit_5 : max_sub_array_partial_solve_wit_5
  proof_of_max_sub_array_partial_solve_wit_6 : max_sub_array_partial_solve_wit_6
  proof_of_max_return_wit_1 : max_return_wit_1
  proof_of_max_return_wit_2 : max_return_wit_2
  proof_of_max_sub_array_safety_wit_6 : max_sub_array_safety_wit_6
  proof_of_max_sub_array_entail_wit_1 : max_sub_array_entail_wit_1
  proof_of_max_sub_array_entail_wit_2 : max_sub_array_entail_wit_2
  proof_of_max_sub_array_return_wit_1 : max_sub_array_return_wit_1

end SimpleC.EE.LLM_bench.Algorithms.maximum_subarray.maximum_subarray_goal
