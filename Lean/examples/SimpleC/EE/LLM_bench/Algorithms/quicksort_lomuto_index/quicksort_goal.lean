import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.quicksort_lomuto_index.quicksort_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.quicksort_lomuto_index.quicksort_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance quicksort_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def swap_return_wit_1 : Prop :=
  forall (l : (List Int)) (n : Int) (arr_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n)) ,
  (intArray.full arr_pre n (replace_Znth (j_pre) ((Znth i_pre l (0 : Int))) ((replace_Znth (i_pre) ((Znth j_pre l (0 : Int))) (l)))))
|--
  (intArray.full arr_pre n (replace_Znth (j_pre) ((Znth (i_pre) (l) ((0 : Int)))) ((replace_Znth (i_pre) ((Znth (j_pre) (l) ((0 : Int)))) (l)))))

noncomputable def swap_partial_solve_wit_1 : Prop :=
  forall (l : (List Int)) (n : Int) (arr_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n)) ,
  (intArray.full arr_pre n l)
|--
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < n) ” &&
  “ ((0 : Int) <= j_pre) ” &&
  “ (j_pre < n) ”
  &&  (((arr_pre + (i_pre * sizeof(INT)))) # Int |-> ((Znth i_pre l (0 : Int))))
  ** (intArray.missing_i arr_pre i_pre (0 : Int) n l)

noncomputable def swap_partial_solve_wit_2 : Prop :=
  forall (l : (List Int)) (n : Int) (arr_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n)) ,
  (intArray.full arr_pre n l)
|--
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < n) ” &&
  “ ((0 : Int) <= j_pre) ” &&
  “ (j_pre < n) ”
  &&  (((arr_pre + (j_pre * sizeof(INT)))) # Int |-> ((Znth j_pre l (0 : Int))))
  ** (intArray.missing_i arr_pre j_pre (0 : Int) n l)

noncomputable def swap_partial_solve_wit_3 : Prop :=
  forall (l : (List Int)) (n : Int) (arr_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n)) ,
  (intArray.full arr_pre n l)
|--
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < n) ” &&
  “ ((0 : Int) <= j_pre) ” &&
  “ (j_pre < n) ”
  &&  (((arr_pre + (i_pre * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i arr_pre i_pre (0 : Int) n l)

noncomputable def swap_partial_solve_wit_4 : Prop :=
  forall (l : (List Int)) (n : Int) (arr_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n)) ,
  (intArray.full arr_pre n (replace_Znth (i_pre) ((Znth j_pre l (0 : Int))) (l)))
|--
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < n) ” &&
  “ ((0 : Int) <= j_pre) ” &&
  “ (j_pre < n) ”
  &&  (((arr_pre + (j_pre * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i arr_pre j_pre (0 : Int) n (replace_Znth (i_pre) ((Znth j_pre l (0 : Int))) (l)))

noncomputable def partition_safety_wit_1 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (PreH1 : ((0 : Int) <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) ,
  ((( &( "i" ) )) # Int |->_)
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "pivot" ) )) # Int |-> ((Znth high_pre l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
|--
  “ ((low_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (low_pre - 1)) ”

noncomputable def partition_safety_wit_2 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (PreH1 : ((0 : Int) <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) ,
  ((( &( "i" ) )) # Int |->_)
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "pivot" ) )) # Int |-> ((Znth high_pre l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def partition_safety_wit_3 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (l1 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : ((Znth j l1 (0 : Int)) <= pivot)) (PreH2 : (j < high_pre)) (PreH3 : (pivot = (Znth high_pre l (0 : Int)))) (PreH4 : ((0 : Int) <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (Permutation l l1)) (PreH11 : (same_outside_range l l1 low_pre high_pre)) (PreH12 : ((Znth high_pre l1 (0 : Int)) = pivot)) (PreH13 : (Forall ((GE.ge (α := Int)) (pivot)) (sublist (low_pre) ((i + 1)) (l1)))) (PreH14 : (Forall ((LT.lt (α := Int)) (pivot)) (sublist ((i + 1)) (j) (l1)))) ,
  (intArray.full arr_pre n_pre l1)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def partition_safety_wit_4 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (l1 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : ((Znth j l1 (0 : Int)) <= pivot)) (PreH2 : (j < high_pre)) (PreH3 : (pivot = (Znth high_pre l (0 : Int)))) (PreH4 : ((0 : Int) <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (Permutation l l1)) (PreH11 : (same_outside_range l l1 low_pre high_pre)) (PreH12 : ((Znth high_pre l1 (0 : Int)) = pivot)) (PreH13 : (Forall ((GE.ge (α := Int)) (pivot)) (sublist (low_pre) ((i + 1)) (l1)))) (PreH14 : (Forall ((LT.lt (α := Int)) (pivot)) (sublist ((i + 1)) (j) (l1)))) ,
  (intArray.full arr_pre n_pre (replace_Znth (j) ((Znth ((i + 1)) (l1) ((0 : Int)))) ((replace_Znth ((i + 1)) ((Znth (j) (l1) ((0 : Int)))) (l1)))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "i" ) )) # Int |-> ((i + 1)))
  ** ((( &( "j" ) )) # Int |-> (j))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def partition_safety_wit_5 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (l1 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : ((Znth j l1 (0 : Int)) > pivot)) (PreH2 : (j < high_pre)) (PreH3 : (pivot = (Znth high_pre l (0 : Int)))) (PreH4 : ((0 : Int) <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (Permutation l l1)) (PreH11 : (same_outside_range l l1 low_pre high_pre)) (PreH12 : ((Znth high_pre l1 (0 : Int)) = pivot)) (PreH13 : (Forall ((GE.ge (α := Int)) (pivot)) (sublist (low_pre) ((i + 1)) (l1)))) (PreH14 : (Forall ((LT.lt (α := Int)) (pivot)) (sublist ((i + 1)) (j) (l1)))) ,
  (intArray.full arr_pre n_pre l1)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def partition_safety_wit_6 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (l1 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : (j >= high_pre)) (PreH2 : (pivot = (Znth high_pre l (0 : Int)))) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (Permutation l l1)) (PreH10 : (same_outside_range l l1 low_pre high_pre)) (PreH11 : ((Znth high_pre l1 (0 : Int)) = pivot)) (PreH12 : (Forall ((GE.ge (α := Int)) (pivot)) (sublist (low_pre) ((i + 1)) (l1)))) (PreH13 : (Forall ((LT.lt (α := Int)) (pivot)) (sublist ((i + 1)) (j) (l1)))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l1)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def partition_safety_wit_7 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (l1 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : (j >= high_pre)) (PreH2 : (pivot = (Znth high_pre l (0 : Int)))) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (Permutation l l1)) (PreH10 : (same_outside_range l l1 low_pre high_pre)) (PreH11 : ((Znth high_pre l1 (0 : Int)) = pivot)) (PreH12 : (Forall ((GE.ge (α := Int)) (pivot)) (sublist (low_pre) ((i + 1)) (l1)))) (PreH13 : (Forall ((LT.lt (α := Int)) (pivot)) (sublist ((i + 1)) (j) (l1)))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l1)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def partition_safety_wit_8 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (l1 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : (j >= high_pre)) (PreH2 : (pivot = (Znth high_pre l (0 : Int)))) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (Permutation l l1)) (PreH10 : (same_outside_range l l1 low_pre high_pre)) (PreH11 : ((Znth high_pre l1 (0 : Int)) = pivot)) (PreH12 : (Forall ((GE.ge (α := Int)) (pivot)) (sublist (low_pre) ((i + 1)) (l1)))) (PreH13 : (Forall ((LT.lt (α := Int)) (pivot)) (sublist ((i + 1)) (j) (l1)))) ,
  (intArray.full arr_pre n_pre (replace_Znth (high_pre) ((Znth ((i + 1)) (l1) ((0 : Int)))) ((replace_Znth ((i + 1)) ((Znth (high_pre) (l1) ((0 : Int)))) (l1)))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "i" ) )) # Int |-> (i))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def partition_safety_wit_9 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (l1 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : (j >= high_pre)) (PreH2 : (pivot = (Znth high_pre l (0 : Int)))) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (Permutation l l1)) (PreH10 : (same_outside_range l l1 low_pre high_pre)) (PreH11 : ((Znth high_pre l1 (0 : Int)) = pivot)) (PreH12 : (Forall ((GE.ge (α := Int)) (pivot)) (sublist (low_pre) ((i + 1)) (l1)))) (PreH13 : (Forall ((LT.lt (α := Int)) (pivot)) (sublist ((i + 1)) (j) (l1)))) ,
  (intArray.full arr_pre n_pre (replace_Znth (high_pre) ((Znth ((i + 1)) (l1) ((0 : Int)))) ((replace_Znth ((i + 1)) ((Znth (high_pre) (l1) ((0 : Int)))) (l1)))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "i" ) )) # Int |-> (i))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def partition_entail_wit_1 : Prop :=
  (
forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (PreH1 : ((0 : Int) <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) ,
  ((( &( "j" ) )) # Int |-> (low_pre))
  ** ((( &( "i" ) )) # Int |-> ((low_pre - 1)))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "pivot" ) )) # Int |-> ((Znth high_pre l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
|--
  EX l1 : (List Int), EX j : Int, EX i : Int, EX pivot : Int,
  “ (pivot = (Znth high_pre l (0 : Int))) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ (high_pre < n_pre) ” &&
  “ ((low_pre - 1) <= i) ” &&
  “ (i < j) ” &&
  “ (j <= high_pre) ” &&
  “ (Permutation l l1) ” &&
  “ (same_outside_range l l1 low_pre high_pre) ” &&
  “ ((Znth high_pre l1 (0 : Int)) = pivot) ” &&
  “ (Forall ((GE.ge (α := Int)) (pivot)) (sublist (low_pre) ((i + 1)) (l1))) ” &&
  “ (Forall ((LT.lt (α := Int)) (pivot)) (sublist ((i + 1)) (j) (l1))) ”
  &&  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full arr_pre n_pre l1)
) \/
(
forall (l : (List Int)) (n_pre : Int) (low_pre : Int) (high_pre : Int) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : ((0 : Int) <= low_pre)) (PreH3 : (low_pre <= high_pre)) (PreH4 : (high_pre < n_pre)) ,
  TT && emp 
|--
  “ (Forall ((LT.lt (α := Int)) ((Znth high_pre l (0 : Int)))) (sublist (((low_pre - 1) + 1)) (low_pre) (l))) ” &&
  “ (Forall ((GE.ge (α := Int)) ((Znth high_pre l (0 : Int)))) (sublist (low_pre) (((low_pre - 1) + 1)) (l))) ” &&
  “ (same_outside_range l l low_pre high_pre) ” &&
  “ (Permutation l l) ”
  &&  emp
)

noncomputable def partition_entail_wit_1_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (low_pre : Int) (high_pre : Int) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : ((0 : Int) <= low_pre)) (PreH3 : (low_pre <= high_pre)) (PreH4 : (high_pre < n_pre)) ,
  (Forall ((LT.lt (α := Int)) ((Znth high_pre l (0 : Int)))) (sublist (((low_pre - 1) + 1)) (low_pre) (l)))

noncomputable def partition_entail_wit_1_split_goal_2 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (low_pre : Int) (high_pre : Int) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : ((0 : Int) <= low_pre)) (PreH3 : (low_pre <= high_pre)) (PreH4 : (high_pre < n_pre)) ,
  (Forall ((GE.ge (α := Int)) ((Znth high_pre l (0 : Int)))) (sublist (low_pre) (((low_pre - 1) + 1)) (l)))

noncomputable def partition_entail_wit_1_split_goal_3 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (low_pre : Int) (high_pre : Int) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : ((0 : Int) <= low_pre)) (PreH3 : (low_pre <= high_pre)) (PreH4 : (high_pre < n_pre)) ,
  (same_outside_range l l low_pre high_pre)

noncomputable def partition_entail_wit_1_split_goal_4 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (low_pre : Int) (high_pre : Int) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : ((0 : Int) <= low_pre)) (PreH3 : (low_pre <= high_pre)) (PreH4 : (high_pre < n_pre)) ,
  (Permutation l l)

noncomputable def partition_entail_wit_2_1 : Prop :=
  (
forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (l1_2 : (List Int)) (j_2 : Int) (i_2 : Int) (pivot_2 : Int) (PreH1 : ((Znth j_2 l1_2 (0 : Int)) <= pivot_2)) (PreH2 : (j_2 < high_pre)) (PreH3 : (pivot_2 = (Znth high_pre l (0 : Int)))) (PreH4 : ((0 : Int) <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1) <= i_2)) (PreH8 : (i_2 < j_2)) (PreH9 : (j_2 <= high_pre)) (PreH10 : (Permutation l l1_2)) (PreH11 : (same_outside_range l l1_2 low_pre high_pre)) (PreH12 : ((Znth high_pre l1_2 (0 : Int)) = pivot_2)) (PreH13 : (Forall ((GE.ge (α := Int)) (pivot_2)) (sublist (low_pre) ((i_2 + 1)) (l1_2)))) (PreH14 : (Forall ((LT.lt (α := Int)) (pivot_2)) (sublist ((i_2 + 1)) (j_2) (l1_2)))) ,
  (intArray.full arr_pre n_pre (replace_Znth (j_2) ((Znth ((i_2 + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i_2 + 1)) ((Znth (j_2) (l1_2) ((0 : Int)))) (l1_2)))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot_2))
  ** ((( &( "i" ) )) # Int |-> ((i_2 + 1)))
  ** ((( &( "j" ) )) # Int |-> ((j_2 + 1)))
|--
  EX l1 : (List Int), EX j : Int, EX i : Int, EX pivot : Int,
  “ (pivot = (Znth high_pre l (0 : Int))) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ (high_pre < n_pre) ” &&
  “ ((low_pre - 1) <= i) ” &&
  “ (i < j) ” &&
  “ (j <= high_pre) ” &&
  “ (Permutation l l1) ” &&
  “ (same_outside_range l l1 low_pre high_pre) ” &&
  “ ((Znth high_pre l1 (0 : Int)) = pivot) ” &&
  “ (Forall ((GE.ge (α := Int)) (pivot)) (sublist (low_pre) ((i + 1)) (l1))) ” &&
  “ (Forall ((LT.lt (α := Int)) (pivot)) (sublist ((i + 1)) (j) (l1))) ”
  &&  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full arr_pre n_pre l1)
) \/
(
forall (l : (List Int)) (n_pre : Int) (low_pre : Int) (high_pre : Int) (l1_2 : (List Int)) (j_2 : Int) (i_2 : Int) (pivot_2 : Int) (PreH1 : ((Zlength ((replace_Znth (j_2) ((Znth ((i_2 + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i_2 + 1)) ((Znth (j_2) (l1_2) ((0 : Int)))) (l1_2)))))) = n_pre)) (PreH2 : ((Znth j_2 l1_2 (0 : Int)) <= pivot_2)) (PreH3 : (j_2 < high_pre)) (PreH4 : (pivot_2 = (Znth high_pre l (0 : Int)))) (PreH5 : ((0 : Int) <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < n_pre)) (PreH8 : ((low_pre - 1) <= i_2)) (PreH9 : (i_2 < j_2)) (PreH10 : (j_2 <= high_pre)) (PreH11 : (Permutation l l1_2)) (PreH12 : (same_outside_range l l1_2 low_pre high_pre)) (PreH13 : ((Znth high_pre l1_2 (0 : Int)) = pivot_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (pivot_2)) (sublist (low_pre) ((i_2 + 1)) (l1_2)))) (PreH15 : (Forall ((LT.lt (α := Int)) (pivot_2)) (sublist ((i_2 + 1)) (j_2) (l1_2)))) ,
  TT && emp 
|--
  “ (Forall ((LT.lt (α := Int)) (pivot_2)) (sublist (((i_2 + 1) + 1)) ((j_2 + 1)) ((replace_Znth (j_2) ((Znth ((i_2 + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i_2 + 1)) ((Znth (j_2) (l1_2) ((0 : Int)))) (l1_2))))))) ” &&
  “ (Forall ((GE.ge (α := Int)) (pivot_2)) (sublist (low_pre) (((i_2 + 1) + 1)) ((replace_Znth (j_2) ((Znth ((i_2 + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i_2 + 1)) ((Znth (j_2) (l1_2) ((0 : Int)))) (l1_2))))))) ” &&
  “ ((Znth high_pre (replace_Znth (j_2) ((Znth ((i_2 + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i_2 + 1)) ((Znth (j_2) (l1_2) ((0 : Int)))) (l1_2)))) (0 : Int)) = pivot_2) ” &&
  “ (same_outside_range l (replace_Znth (j_2) ((Znth ((i_2 + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i_2 + 1)) ((Znth (j_2) (l1_2) ((0 : Int)))) (l1_2)))) low_pre high_pre) ” &&
  “ (Permutation l (replace_Znth (j_2) ((Znth ((i_2 + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i_2 + 1)) ((Znth (j_2) (l1_2) ((0 : Int)))) (l1_2))))) ”
  &&  emp
)

noncomputable def partition_entail_wit_2_1_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (low_pre : Int) (high_pre : Int) (l1_2 : (List Int)) (j_2 : Int) (i_2 : Int) (pivot_2 : Int) (PreH1 : ((Zlength ((replace_Znth (j_2) ((Znth ((i_2 + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i_2 + 1)) ((Znth (j_2) (l1_2) ((0 : Int)))) (l1_2)))))) = n_pre)) (PreH2 : ((Znth j_2 l1_2 (0 : Int)) <= pivot_2)) (PreH3 : (j_2 < high_pre)) (PreH4 : (pivot_2 = (Znth high_pre l (0 : Int)))) (PreH5 : ((0 : Int) <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < n_pre)) (PreH8 : ((low_pre - 1) <= i_2)) (PreH9 : (i_2 < j_2)) (PreH10 : (j_2 <= high_pre)) (PreH11 : (Permutation l l1_2)) (PreH12 : (same_outside_range l l1_2 low_pre high_pre)) (PreH13 : ((Znth high_pre l1_2 (0 : Int)) = pivot_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (pivot_2)) (sublist (low_pre) ((i_2 + 1)) (l1_2)))) (PreH15 : (Forall ((LT.lt (α := Int)) (pivot_2)) (sublist ((i_2 + 1)) (j_2) (l1_2)))) ,
  (Forall ((LT.lt (α := Int)) (pivot_2)) (sublist (((i_2 + 1) + 1)) ((j_2 + 1)) ((replace_Znth (j_2) ((Znth ((i_2 + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i_2 + 1)) ((Znth (j_2) (l1_2) ((0 : Int)))) (l1_2)))))))

noncomputable def partition_entail_wit_2_1_split_goal_2 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (low_pre : Int) (high_pre : Int) (l1_2 : (List Int)) (j_2 : Int) (i_2 : Int) (pivot_2 : Int) (PreH1 : ((Zlength ((replace_Znth (j_2) ((Znth ((i_2 + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i_2 + 1)) ((Znth (j_2) (l1_2) ((0 : Int)))) (l1_2)))))) = n_pre)) (PreH2 : ((Znth j_2 l1_2 (0 : Int)) <= pivot_2)) (PreH3 : (j_2 < high_pre)) (PreH4 : (pivot_2 = (Znth high_pre l (0 : Int)))) (PreH5 : ((0 : Int) <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < n_pre)) (PreH8 : ((low_pre - 1) <= i_2)) (PreH9 : (i_2 < j_2)) (PreH10 : (j_2 <= high_pre)) (PreH11 : (Permutation l l1_2)) (PreH12 : (same_outside_range l l1_2 low_pre high_pre)) (PreH13 : ((Znth high_pre l1_2 (0 : Int)) = pivot_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (pivot_2)) (sublist (low_pre) ((i_2 + 1)) (l1_2)))) (PreH15 : (Forall ((LT.lt (α := Int)) (pivot_2)) (sublist ((i_2 + 1)) (j_2) (l1_2)))) ,
  (Forall ((GE.ge (α := Int)) (pivot_2)) (sublist (low_pre) (((i_2 + 1) + 1)) ((replace_Znth (j_2) ((Znth ((i_2 + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i_2 + 1)) ((Znth (j_2) (l1_2) ((0 : Int)))) (l1_2)))))))

noncomputable def partition_entail_wit_2_1_split_goal_3 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (low_pre : Int) (high_pre : Int) (l1_2 : (List Int)) (j_2 : Int) (i_2 : Int) (pivot_2 : Int) (PreH1 : ((Zlength ((replace_Znth (j_2) ((Znth ((i_2 + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i_2 + 1)) ((Znth (j_2) (l1_2) ((0 : Int)))) (l1_2)))))) = n_pre)) (PreH2 : ((Znth j_2 l1_2 (0 : Int)) <= pivot_2)) (PreH3 : (j_2 < high_pre)) (PreH4 : (pivot_2 = (Znth high_pre l (0 : Int)))) (PreH5 : ((0 : Int) <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < n_pre)) (PreH8 : ((low_pre - 1) <= i_2)) (PreH9 : (i_2 < j_2)) (PreH10 : (j_2 <= high_pre)) (PreH11 : (Permutation l l1_2)) (PreH12 : (same_outside_range l l1_2 low_pre high_pre)) (PreH13 : ((Znth high_pre l1_2 (0 : Int)) = pivot_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (pivot_2)) (sublist (low_pre) ((i_2 + 1)) (l1_2)))) (PreH15 : (Forall ((LT.lt (α := Int)) (pivot_2)) (sublist ((i_2 + 1)) (j_2) (l1_2)))) ,
  ((Znth high_pre (replace_Znth (j_2) ((Znth ((i_2 + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i_2 + 1)) ((Znth (j_2) (l1_2) ((0 : Int)))) (l1_2)))) (0 : Int)) = pivot_2)

noncomputable def partition_entail_wit_2_1_split_goal_4 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (low_pre : Int) (high_pre : Int) (l1_2 : (List Int)) (j_2 : Int) (i_2 : Int) (pivot_2 : Int) (PreH1 : ((Zlength ((replace_Znth (j_2) ((Znth ((i_2 + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i_2 + 1)) ((Znth (j_2) (l1_2) ((0 : Int)))) (l1_2)))))) = n_pre)) (PreH2 : ((Znth j_2 l1_2 (0 : Int)) <= pivot_2)) (PreH3 : (j_2 < high_pre)) (PreH4 : (pivot_2 = (Znth high_pre l (0 : Int)))) (PreH5 : ((0 : Int) <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < n_pre)) (PreH8 : ((low_pre - 1) <= i_2)) (PreH9 : (i_2 < j_2)) (PreH10 : (j_2 <= high_pre)) (PreH11 : (Permutation l l1_2)) (PreH12 : (same_outside_range l l1_2 low_pre high_pre)) (PreH13 : ((Znth high_pre l1_2 (0 : Int)) = pivot_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (pivot_2)) (sublist (low_pre) ((i_2 + 1)) (l1_2)))) (PreH15 : (Forall ((LT.lt (α := Int)) (pivot_2)) (sublist ((i_2 + 1)) (j_2) (l1_2)))) ,
  (same_outside_range l (replace_Znth (j_2) ((Znth ((i_2 + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i_2 + 1)) ((Znth (j_2) (l1_2) ((0 : Int)))) (l1_2)))) low_pre high_pre)

noncomputable def partition_entail_wit_2_1_split_goal_5 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (low_pre : Int) (high_pre : Int) (l1_2 : (List Int)) (j_2 : Int) (i_2 : Int) (pivot_2 : Int) (PreH1 : ((Zlength ((replace_Znth (j_2) ((Znth ((i_2 + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i_2 + 1)) ((Znth (j_2) (l1_2) ((0 : Int)))) (l1_2)))))) = n_pre)) (PreH2 : ((Znth j_2 l1_2 (0 : Int)) <= pivot_2)) (PreH3 : (j_2 < high_pre)) (PreH4 : (pivot_2 = (Znth high_pre l (0 : Int)))) (PreH5 : ((0 : Int) <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < n_pre)) (PreH8 : ((low_pre - 1) <= i_2)) (PreH9 : (i_2 < j_2)) (PreH10 : (j_2 <= high_pre)) (PreH11 : (Permutation l l1_2)) (PreH12 : (same_outside_range l l1_2 low_pre high_pre)) (PreH13 : ((Znth high_pre l1_2 (0 : Int)) = pivot_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (pivot_2)) (sublist (low_pre) ((i_2 + 1)) (l1_2)))) (PreH15 : (Forall ((LT.lt (α := Int)) (pivot_2)) (sublist ((i_2 + 1)) (j_2) (l1_2)))) ,
  (Permutation l (replace_Znth (j_2) ((Znth ((i_2 + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i_2 + 1)) ((Znth (j_2) (l1_2) ((0 : Int)))) (l1_2)))))

noncomputable def partition_entail_wit_2_2 : Prop :=
  (
forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (l1_2 : (List Int)) (j_2 : Int) (i_2 : Int) (pivot_2 : Int) (PreH1 : ((Znth j_2 l1_2 (0 : Int)) > pivot_2)) (PreH2 : (j_2 < high_pre)) (PreH3 : (pivot_2 = (Znth high_pre l (0 : Int)))) (PreH4 : ((0 : Int) <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1) <= i_2)) (PreH8 : (i_2 < j_2)) (PreH9 : (j_2 <= high_pre)) (PreH10 : (Permutation l l1_2)) (PreH11 : (same_outside_range l l1_2 low_pre high_pre)) (PreH12 : ((Znth high_pre l1_2 (0 : Int)) = pivot_2)) (PreH13 : (Forall ((GE.ge (α := Int)) (pivot_2)) (sublist (low_pre) ((i_2 + 1)) (l1_2)))) (PreH14 : (Forall ((LT.lt (α := Int)) (pivot_2)) (sublist ((i_2 + 1)) (j_2) (l1_2)))) ,
  (intArray.full arr_pre n_pre l1_2)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot_2))
  ** ((( &( "i" ) )) # Int |-> (i_2))
  ** ((( &( "j" ) )) # Int |-> ((j_2 + 1)))
|--
  EX l1 : (List Int), EX j : Int, EX i : Int, EX pivot : Int,
  “ (pivot = (Znth high_pre l (0 : Int))) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ (high_pre < n_pre) ” &&
  “ ((low_pre - 1) <= i) ” &&
  “ (i < j) ” &&
  “ (j <= high_pre) ” &&
  “ (Permutation l l1) ” &&
  “ (same_outside_range l l1 low_pre high_pre) ” &&
  “ ((Znth high_pre l1 (0 : Int)) = pivot) ” &&
  “ (Forall ((GE.ge (α := Int)) (pivot)) (sublist (low_pre) ((i + 1)) (l1))) ” &&
  “ (Forall ((LT.lt (α := Int)) (pivot)) (sublist ((i + 1)) (j) (l1))) ”
  &&  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full arr_pre n_pre l1)
) \/
(
forall (l : (List Int)) (n_pre : Int) (low_pre : Int) (high_pre : Int) (l1_2 : (List Int)) (j_2 : Int) (i_2 : Int) (pivot_2 : Int) (PreH1 : ((Zlength (l1_2)) = n_pre)) (PreH2 : ((Znth j_2 l1_2 (0 : Int)) > pivot_2)) (PreH3 : (j_2 < high_pre)) (PreH4 : (pivot_2 = (Znth high_pre l (0 : Int)))) (PreH5 : ((0 : Int) <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < n_pre)) (PreH8 : ((low_pre - 1) <= i_2)) (PreH9 : (i_2 < j_2)) (PreH10 : (j_2 <= high_pre)) (PreH11 : (Permutation l l1_2)) (PreH12 : (same_outside_range l l1_2 low_pre high_pre)) (PreH13 : ((Znth high_pre l1_2 (0 : Int)) = pivot_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (pivot_2)) (sublist (low_pre) ((i_2 + 1)) (l1_2)))) (PreH15 : (Forall ((LT.lt (α := Int)) (pivot_2)) (sublist ((i_2 + 1)) (j_2) (l1_2)))) ,
  TT && emp 
|--
  “ (Forall ((LT.lt (α := Int)) (pivot_2)) (sublist ((i_2 + 1)) ((j_2 + 1)) (l1_2))) ”
  &&  emp
)

noncomputable def partition_entail_wit_2_2_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (low_pre : Int) (high_pre : Int) (l1_2 : (List Int)) (j_2 : Int) (i_2 : Int) (pivot_2 : Int) (PreH1 : ((Zlength (l1_2)) = n_pre)) (PreH2 : ((Znth j_2 l1_2 (0 : Int)) > pivot_2)) (PreH3 : (j_2 < high_pre)) (PreH4 : (pivot_2 = (Znth high_pre l (0 : Int)))) (PreH5 : ((0 : Int) <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < n_pre)) (PreH8 : ((low_pre - 1) <= i_2)) (PreH9 : (i_2 < j_2)) (PreH10 : (j_2 <= high_pre)) (PreH11 : (Permutation l l1_2)) (PreH12 : (same_outside_range l l1_2 low_pre high_pre)) (PreH13 : ((Znth high_pre l1_2 (0 : Int)) = pivot_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (pivot_2)) (sublist (low_pre) ((i_2 + 1)) (l1_2)))) (PreH15 : (Forall ((LT.lt (α := Int)) (pivot_2)) (sublist ((i_2 + 1)) (j_2) (l1_2)))) ,
  (Forall ((LT.lt (α := Int)) (pivot_2)) (sublist ((i_2 + 1)) ((j_2 + 1)) (l1_2)))

noncomputable def partition_return_wit_1 : Prop :=
  (
forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (l1_2 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : (j >= high_pre)) (PreH2 : (pivot = (Znth high_pre l (0 : Int)))) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (Permutation l l1_2)) (PreH10 : (same_outside_range l l1_2 low_pre high_pre)) (PreH11 : ((Znth high_pre l1_2 (0 : Int)) = pivot)) (PreH12 : (Forall ((GE.ge (α := Int)) (pivot)) (sublist (low_pre) ((i + 1)) (l1_2)))) (PreH13 : (Forall ((LT.lt (α := Int)) (pivot)) (sublist ((i + 1)) (j) (l1_2)))) ,
  (intArray.full arr_pre n_pre (replace_Znth (high_pre) ((Znth ((i + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i + 1)) ((Znth (high_pre) (l1_2) ((0 : Int)))) (l1_2)))))
|--
  EX l1 : (List Int),
  “ (low_pre <= (i + 1)) ” &&
  “ ((i + 1) <= high_pre) ” &&
  “ (Permutation l l1) ” &&
  “ (same_outside_range l l1 low_pre high_pre) ” &&
  “ (partitioned_at l1 low_pre high_pre (i + 1)) ”
  &&  (intArray.full arr_pre n_pre l1)
) \/
(
forall (l : (List Int)) (n_pre : Int) (low_pre : Int) (high_pre : Int) (l1_2 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : ((Zlength ((replace_Znth (high_pre) ((Znth ((i + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i + 1)) ((Znth (high_pre) (l1_2) ((0 : Int)))) (l1_2)))))) = n_pre)) (PreH2 : (j >= high_pre)) (PreH3 : (pivot = (Znth high_pre l (0 : Int)))) (PreH4 : ((0 : Int) <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (Permutation l l1_2)) (PreH11 : (same_outside_range l l1_2 low_pre high_pre)) (PreH12 : ((Znth high_pre l1_2 (0 : Int)) = pivot)) (PreH13 : (Forall ((GE.ge (α := Int)) (pivot)) (sublist (low_pre) ((i + 1)) (l1_2)))) (PreH14 : (Forall ((LT.lt (α := Int)) (pivot)) (sublist ((i + 1)) (j) (l1_2)))) ,
  TT && emp 
|--
  “ (partitioned_at (replace_Znth (high_pre) ((Znth ((i + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i + 1)) (pivot) (l1_2)))) low_pre high_pre (i + 1)) ” &&
  “ (same_outside_range l (replace_Znth (high_pre) ((Znth ((i + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i + 1)) (pivot) (l1_2)))) low_pre high_pre) ” &&
  “ (Permutation l (replace_Znth (high_pre) ((Znth ((i + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i + 1)) (pivot) (l1_2))))) ”
  &&  emp
)

noncomputable def partition_return_wit_1_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (low_pre : Int) (high_pre : Int) (l1_2 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : ((Zlength ((replace_Znth (high_pre) ((Znth ((i + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i + 1)) ((Znth (high_pre) (l1_2) ((0 : Int)))) (l1_2)))))) = n_pre)) (PreH2 : (j >= high_pre)) (PreH3 : (pivot = (Znth high_pre l (0 : Int)))) (PreH4 : ((0 : Int) <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (Permutation l l1_2)) (PreH11 : (same_outside_range l l1_2 low_pre high_pre)) (PreH12 : ((Znth high_pre l1_2 (0 : Int)) = pivot)) (PreH13 : (Forall ((GE.ge (α := Int)) (pivot)) (sublist (low_pre) ((i + 1)) (l1_2)))) (PreH14 : (Forall ((LT.lt (α := Int)) (pivot)) (sublist ((i + 1)) (j) (l1_2)))) ,
  (partitioned_at (replace_Znth (high_pre) ((Znth ((i + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i + 1)) (pivot) (l1_2)))) low_pre high_pre (i + 1))

noncomputable def partition_return_wit_1_split_goal_2 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (low_pre : Int) (high_pre : Int) (l1_2 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : ((Zlength ((replace_Znth (high_pre) ((Znth ((i + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i + 1)) ((Znth (high_pre) (l1_2) ((0 : Int)))) (l1_2)))))) = n_pre)) (PreH2 : (j >= high_pre)) (PreH3 : (pivot = (Znth high_pre l (0 : Int)))) (PreH4 : ((0 : Int) <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (Permutation l l1_2)) (PreH11 : (same_outside_range l l1_2 low_pre high_pre)) (PreH12 : ((Znth high_pre l1_2 (0 : Int)) = pivot)) (PreH13 : (Forall ((GE.ge (α := Int)) (pivot)) (sublist (low_pre) ((i + 1)) (l1_2)))) (PreH14 : (Forall ((LT.lt (α := Int)) (pivot)) (sublist ((i + 1)) (j) (l1_2)))) ,
  (same_outside_range l (replace_Znth (high_pre) ((Znth ((i + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i + 1)) (pivot) (l1_2)))) low_pre high_pre)

noncomputable def partition_return_wit_1_split_goal_3 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (low_pre : Int) (high_pre : Int) (l1_2 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : ((Zlength ((replace_Znth (high_pre) ((Znth ((i + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i + 1)) ((Znth (high_pre) (l1_2) ((0 : Int)))) (l1_2)))))) = n_pre)) (PreH2 : (j >= high_pre)) (PreH3 : (pivot = (Znth high_pre l (0 : Int)))) (PreH4 : ((0 : Int) <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (Permutation l l1_2)) (PreH11 : (same_outside_range l l1_2 low_pre high_pre)) (PreH12 : ((Znth high_pre l1_2 (0 : Int)) = pivot)) (PreH13 : (Forall ((GE.ge (α := Int)) (pivot)) (sublist (low_pre) ((i + 1)) (l1_2)))) (PreH14 : (Forall ((LT.lt (α := Int)) (pivot)) (sublist ((i + 1)) (j) (l1_2)))) ,
  (Permutation l (replace_Znth (high_pre) ((Znth ((i + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i + 1)) (pivot) (l1_2)))))

noncomputable def partition_partial_solve_wit_1 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (PreH1 : ((0 : Int) <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) ,
  (intArray.full arr_pre n_pre l)
|--
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ (high_pre < n_pre) ”
  &&  (((arr_pre + (high_pre * sizeof(INT)))) # Int |-> ((Znth high_pre l (0 : Int))))
  ** (intArray.missing_i arr_pre high_pre (0 : Int) n_pre l)

noncomputable def partition_partial_solve_wit_2 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (l1 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : (j < high_pre)) (PreH2 : (pivot = (Znth high_pre l (0 : Int)))) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (Permutation l l1)) (PreH10 : (same_outside_range l l1 low_pre high_pre)) (PreH11 : ((Znth high_pre l1 (0 : Int)) = pivot)) (PreH12 : (Forall ((GE.ge (α := Int)) (pivot)) (sublist (low_pre) ((i + 1)) (l1)))) (PreH13 : (Forall ((LT.lt (α := Int)) (pivot)) (sublist ((i + 1)) (j) (l1)))) ,
  (intArray.full arr_pre n_pre l1)
|--
  “ (j < high_pre) ” &&
  “ (pivot = (Znth high_pre l (0 : Int))) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ (high_pre < n_pre) ” &&
  “ ((low_pre - 1) <= i) ” &&
  “ (i < j) ” &&
  “ (j <= high_pre) ” &&
  “ (Permutation l l1) ” &&
  “ (same_outside_range l l1 low_pre high_pre) ” &&
  “ ((Znth high_pre l1 (0 : Int)) = pivot) ” &&
  “ (Forall ((GE.ge (α := Int)) (pivot)) (sublist (low_pre) ((i + 1)) (l1))) ” &&
  “ (Forall ((LT.lt (α := Int)) (pivot)) (sublist ((i + 1)) (j) (l1))) ”
  &&  (((arr_pre + (j * sizeof(INT)))) # Int |-> ((Znth j l1 (0 : Int))))
  ** (intArray.missing_i arr_pre j (0 : Int) n_pre l1)

noncomputable def partition_partial_solve_wit_3_pure : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (l1 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : ((Znth j l1 (0 : Int)) <= pivot)) (PreH2 : (j < high_pre)) (PreH3 : (pivot = (Znth high_pre l (0 : Int)))) (PreH4 : ((0 : Int) <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (Permutation l l1)) (PreH11 : (same_outside_range l l1 low_pre high_pre)) (PreH12 : ((Znth high_pre l1 (0 : Int)) = pivot)) (PreH13 : (Forall ((GE.ge (α := Int)) (pivot)) (sublist (low_pre) ((i + 1)) (l1)))) (PreH14 : (Forall ((LT.lt (α := Int)) (pivot)) (sublist ((i + 1)) (j) (l1)))) ,
  (intArray.full arr_pre n_pre l1)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "i" ) )) # Int |-> ((i + 1)))
  ** ((( &( "j" ) )) # Int |-> (j))
|--
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) < n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < n_pre) ”

noncomputable def partition_partial_solve_wit_3_aux : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (l1 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : ((Znth j l1 (0 : Int)) <= pivot)) (PreH2 : (j < high_pre)) (PreH3 : (pivot = (Znth high_pre l (0 : Int)))) (PreH4 : ((0 : Int) <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (Permutation l l1)) (PreH11 : (same_outside_range l l1 low_pre high_pre)) (PreH12 : ((Znth high_pre l1 (0 : Int)) = pivot)) (PreH13 : (Forall ((GE.ge (α := Int)) (pivot)) (sublist (low_pre) ((i + 1)) (l1)))) (PreH14 : (Forall ((LT.lt (α := Int)) (pivot)) (sublist ((i + 1)) (j) (l1)))) ,
  (intArray.full arr_pre n_pre l1)
|--
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) < n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < n_pre) ” &&
  “ ((Znth j l1 (0 : Int)) <= pivot) ” &&
  “ (j < high_pre) ” &&
  “ (pivot = (Znth high_pre l (0 : Int))) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ (high_pre < n_pre) ” &&
  “ ((low_pre - 1) <= i) ” &&
  “ (i < j) ” &&
  “ (j <= high_pre) ” &&
  “ (Permutation l l1) ” &&
  “ (same_outside_range l l1 low_pre high_pre) ” &&
  “ ((Znth high_pre l1 (0 : Int)) = pivot) ” &&
  “ (Forall ((GE.ge (α := Int)) (pivot)) (sublist (low_pre) ((i + 1)) (l1))) ” &&
  “ (Forall ((LT.lt (α := Int)) (pivot)) (sublist ((i + 1)) (j) (l1))) ”
  &&  (intArray.full arr_pre n_pre l1)

noncomputable def partition_partial_solve_wit_3 : Prop := partition_partial_solve_wit_3_pure -> partition_partial_solve_wit_3_aux

noncomputable def partition_partial_solve_wit_4_pure : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (l1 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : (j >= high_pre)) (PreH2 : (pivot = (Znth high_pre l (0 : Int)))) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (Permutation l l1)) (PreH10 : (same_outside_range l l1 low_pre high_pre)) (PreH11 : ((Znth high_pre l1 (0 : Int)) = pivot)) (PreH12 : (Forall ((GE.ge (α := Int)) (pivot)) (sublist (low_pre) ((i + 1)) (l1)))) (PreH13 : (Forall ((LT.lt (α := Int)) (pivot)) (sublist ((i + 1)) (j) (l1)))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l1)
|--
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) < n_pre) ” &&
  “ ((0 : Int) <= high_pre) ” &&
  “ (high_pre < n_pre) ”

noncomputable def partition_partial_solve_wit_4_aux : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (l1 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : (j >= high_pre)) (PreH2 : (pivot = (Znth high_pre l (0 : Int)))) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (Permutation l l1)) (PreH10 : (same_outside_range l l1 low_pre high_pre)) (PreH11 : ((Znth high_pre l1 (0 : Int)) = pivot)) (PreH12 : (Forall ((GE.ge (α := Int)) (pivot)) (sublist (low_pre) ((i + 1)) (l1)))) (PreH13 : (Forall ((LT.lt (α := Int)) (pivot)) (sublist ((i + 1)) (j) (l1)))) ,
  (intArray.full arr_pre n_pre l1)
|--
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) < n_pre) ” &&
  “ ((0 : Int) <= high_pre) ” &&
  “ (high_pre < n_pre) ” &&
  “ (j >= high_pre) ” &&
  “ (pivot = (Znth high_pre l (0 : Int))) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ (high_pre < n_pre) ” &&
  “ ((low_pre - 1) <= i) ” &&
  “ (i < j) ” &&
  “ (j <= high_pre) ” &&
  “ (Permutation l l1) ” &&
  “ (same_outside_range l l1 low_pre high_pre) ” &&
  “ ((Znth high_pre l1 (0 : Int)) = pivot) ” &&
  “ (Forall ((GE.ge (α := Int)) (pivot)) (sublist (low_pre) ((i + 1)) (l1))) ” &&
  “ (Forall ((LT.lt (α := Int)) (pivot)) (sublist ((i + 1)) (j) (l1))) ”
  &&  (intArray.full arr_pre n_pre l1)

noncomputable def partition_partial_solve_wit_4 : Prop := partition_partial_solve_wit_4_pure -> partition_partial_solve_wit_4_aux

noncomputable def quicksort_range_safety_wit_1 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (l1 : (List Int)) (retval : Int) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (Permutation l l1)) (PreH5 : (same_outside_range l l1 left_pre right_pre)) (PreH6 : (partitioned_at l1 left_pre right_pre retval)) (PreH7 : (left_pre < right_pre)) (PreH8 : ((0 : Int) <= n_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : ((-1) <= right_pre)) (PreH11 : (right_pre < n_pre)) ,
  (intArray.full arr_pre n_pre l1)
  ** ((( &( "p" ) )) # Int |-> (retval))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ ((retval - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (retval - 1)) ”

noncomputable def quicksort_range_safety_wit_2 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (l1 : (List Int)) (retval : Int) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (Permutation l l1)) (PreH5 : (same_outside_range l l1 left_pre right_pre)) (PreH6 : (partitioned_at l1 left_pre right_pre retval)) (PreH7 : (left_pre < right_pre)) (PreH8 : ((0 : Int) <= n_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : ((-1) <= right_pre)) (PreH11 : (right_pre < n_pre)) ,
  (intArray.full arr_pre n_pre l1)
  ** ((( &( "p" ) )) # Int |-> (retval))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def quicksort_range_safety_wit_3 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (l1 : (List Int)) (retval : Int) (PreH1 : (retval >= right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (Permutation l l1)) (PreH6 : (same_outside_range l l1 left_pre right_pre)) (PreH7 : (partitioned_at l1 left_pre right_pre retval)) (PreH8 : (left_pre < right_pre)) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : ((-1) <= right_pre)) (PreH12 : (right_pre < n_pre)) ,
  (intArray.full arr_pre n_pre l1)
  ** ((( &( "p" ) )) # Int |-> (retval))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ False ”

noncomputable def quicksort_range_safety_wit_4 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (l1 : (List Int)) (retval : Int) (l1_2 : (List Int)) (PreH1 : (retval < right_pre)) (PreH2 : (Permutation l1 l1_2)) (PreH3 : (same_outside_range l1 l1_2 left_pre (retval - 1))) (PreH4 : (range_nondecreasing l1_2 left_pre (retval - 1))) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (Permutation l l1)) (PreH9 : (same_outside_range l l1 left_pre right_pre)) (PreH10 : (partitioned_at l1 left_pre right_pre retval)) (PreH11 : (left_pre < right_pre)) (PreH12 : ((0 : Int) <= n_pre)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
  (intArray.full arr_pre n_pre l1_2)
  ** ((( &( "p" ) )) # Int |-> (retval))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ ((retval + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (retval + 1)) ”

noncomputable def quicksort_range_safety_wit_5 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (l1 : (List Int)) (retval : Int) (l1_2 : (List Int)) (PreH1 : (retval < right_pre)) (PreH2 : (Permutation l1 l1_2)) (PreH3 : (same_outside_range l1 l1_2 left_pre (retval - 1))) (PreH4 : (range_nondecreasing l1_2 left_pre (retval - 1))) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (Permutation l l1)) (PreH9 : (same_outside_range l l1 left_pre right_pre)) (PreH10 : (partitioned_at l1 left_pre right_pre retval)) (PreH11 : (left_pre < right_pre)) (PreH12 : ((0 : Int) <= n_pre)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
  (intArray.full arr_pre n_pre l1_2)
  ** ((( &( "p" ) )) # Int |-> (retval))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def quicksort_range_safety_wit_6 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (l1 : (List Int)) (retval : Int) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (Permutation l l1)) (PreH6 : (same_outside_range l l1 left_pre right_pre)) (PreH7 : (partitioned_at l1 left_pre right_pre retval)) (PreH8 : (left_pre < right_pre)) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : ((-1) <= right_pre)) (PreH12 : (right_pre < n_pre)) ,
  (intArray.full arr_pre n_pre l1)
  ** ((( &( "p" ) )) # Int |-> (retval))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ ((retval + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (retval + 1)) ”

noncomputable def quicksort_range_safety_wit_7 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (l1 : (List Int)) (retval : Int) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (Permutation l l1)) (PreH6 : (same_outside_range l l1 left_pre right_pre)) (PreH7 : (partitioned_at l1 left_pre right_pre retval)) (PreH8 : (left_pre < right_pre)) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : ((-1) <= right_pre)) (PreH12 : (right_pre < n_pre)) ,
  (intArray.full arr_pre n_pre l1)
  ** ((( &( "p" ) )) # Int |-> (retval))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def quicksort_range_return_wit_1 : Prop :=
  (
forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (l1_2 : (List Int)) (retval : Int) (l1_3 : (List Int)) (l1_4 : (List Int)) (PreH1 : (Permutation l1_3 l1_4)) (PreH2 : (same_outside_range l1_3 l1_4 (retval + 1) right_pre)) (PreH3 : (range_nondecreasing l1_4 (retval + 1) right_pre)) (PreH4 : (retval < right_pre)) (PreH5 : (Permutation l1_2 l1_3)) (PreH6 : (same_outside_range l1_2 l1_3 left_pre (retval - 1))) (PreH7 : (range_nondecreasing l1_3 left_pre (retval - 1))) (PreH8 : (retval > left_pre)) (PreH9 : (left_pre <= retval)) (PreH10 : (retval <= right_pre)) (PreH11 : (Permutation l l1_2)) (PreH12 : (same_outside_range l l1_2 left_pre right_pre)) (PreH13 : (partitioned_at l1_2 left_pre right_pre retval)) (PreH14 : (left_pre < right_pre)) (PreH15 : ((0 : Int) <= n_pre)) (PreH16 : ((0 : Int) <= left_pre)) (PreH17 : ((-1) <= right_pre)) (PreH18 : (right_pre < n_pre)) ,
  (intArray.full arr_pre n_pre l1_4)
|--
  EX l1 : (List Int),
  “ (Permutation l l1) ” &&
  “ (same_outside_range l l1 left_pre right_pre) ” &&
  “ (range_nondecreasing l1 left_pre right_pre) ”
  &&  (intArray.full arr_pre n_pre l1)
) \/
(
forall (l : (List Int)) (n_pre : Int) (left_pre : Int) (right_pre : Int) (l1_2 : (List Int)) (retval : Int) (l1_3 : (List Int)) (l1_4 : (List Int)) (PreH1 : ((Zlength (l1_4)) = n_pre)) (PreH2 : (Permutation l1_3 l1_4)) (PreH3 : (same_outside_range l1_3 l1_4 (retval + 1) right_pre)) (PreH4 : (range_nondecreasing l1_4 (retval + 1) right_pre)) (PreH5 : (retval < right_pre)) (PreH6 : (Permutation l1_2 l1_3)) (PreH7 : (same_outside_range l1_2 l1_3 left_pre (retval - 1))) (PreH8 : (range_nondecreasing l1_3 left_pre (retval - 1))) (PreH9 : (retval > left_pre)) (PreH10 : (left_pre <= retval)) (PreH11 : (retval <= right_pre)) (PreH12 : (Permutation l l1_2)) (PreH13 : (same_outside_range l l1_2 left_pre right_pre)) (PreH14 : (partitioned_at l1_2 left_pre right_pre retval)) (PreH15 : (left_pre < right_pre)) (PreH16 : ((0 : Int) <= n_pre)) (PreH17 : ((0 : Int) <= left_pre)) (PreH18 : ((-1) <= right_pre)) (PreH19 : (right_pre < n_pre)) ,
  TT && emp 
|--
  “ (range_nondecreasing l1_4 left_pre right_pre) ” &&
  “ (same_outside_range l l1_4 left_pre right_pre) ” &&
  “ (Permutation l l1_4) ”
  &&  emp
)

noncomputable def quicksort_range_return_wit_1_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (left_pre : Int) (right_pre : Int) (l1_2 : (List Int)) (retval : Int) (l1_3 : (List Int)) (l1_4 : (List Int)) (PreH1 : ((Zlength (l1_4)) = n_pre)) (PreH2 : (Permutation l1_3 l1_4)) (PreH3 : (same_outside_range l1_3 l1_4 (retval + 1) right_pre)) (PreH4 : (range_nondecreasing l1_4 (retval + 1) right_pre)) (PreH5 : (retval < right_pre)) (PreH6 : (Permutation l1_2 l1_3)) (PreH7 : (same_outside_range l1_2 l1_3 left_pre (retval - 1))) (PreH8 : (range_nondecreasing l1_3 left_pre (retval - 1))) (PreH9 : (retval > left_pre)) (PreH10 : (left_pre <= retval)) (PreH11 : (retval <= right_pre)) (PreH12 : (Permutation l l1_2)) (PreH13 : (same_outside_range l l1_2 left_pre right_pre)) (PreH14 : (partitioned_at l1_2 left_pre right_pre retval)) (PreH15 : (left_pre < right_pre)) (PreH16 : ((0 : Int) <= n_pre)) (PreH17 : ((0 : Int) <= left_pre)) (PreH18 : ((-1) <= right_pre)) (PreH19 : (right_pre < n_pre)) ,
  (range_nondecreasing l1_4 left_pre right_pre)

noncomputable def quicksort_range_return_wit_1_split_goal_2 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (left_pre : Int) (right_pre : Int) (l1_2 : (List Int)) (retval : Int) (l1_3 : (List Int)) (l1_4 : (List Int)) (PreH1 : ((Zlength (l1_4)) = n_pre)) (PreH2 : (Permutation l1_3 l1_4)) (PreH3 : (same_outside_range l1_3 l1_4 (retval + 1) right_pre)) (PreH4 : (range_nondecreasing l1_4 (retval + 1) right_pre)) (PreH5 : (retval < right_pre)) (PreH6 : (Permutation l1_2 l1_3)) (PreH7 : (same_outside_range l1_2 l1_3 left_pre (retval - 1))) (PreH8 : (range_nondecreasing l1_3 left_pre (retval - 1))) (PreH9 : (retval > left_pre)) (PreH10 : (left_pre <= retval)) (PreH11 : (retval <= right_pre)) (PreH12 : (Permutation l l1_2)) (PreH13 : (same_outside_range l l1_2 left_pre right_pre)) (PreH14 : (partitioned_at l1_2 left_pre right_pre retval)) (PreH15 : (left_pre < right_pre)) (PreH16 : ((0 : Int) <= n_pre)) (PreH17 : ((0 : Int) <= left_pre)) (PreH18 : ((-1) <= right_pre)) (PreH19 : (right_pre < n_pre)) ,
  (same_outside_range l l1_4 left_pre right_pre)

noncomputable def quicksort_range_return_wit_1_split_goal_3 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (left_pre : Int) (right_pre : Int) (l1_2 : (List Int)) (retval : Int) (l1_3 : (List Int)) (l1_4 : (List Int)) (PreH1 : ((Zlength (l1_4)) = n_pre)) (PreH2 : (Permutation l1_3 l1_4)) (PreH3 : (same_outside_range l1_3 l1_4 (retval + 1) right_pre)) (PreH4 : (range_nondecreasing l1_4 (retval + 1) right_pre)) (PreH5 : (retval < right_pre)) (PreH6 : (Permutation l1_2 l1_3)) (PreH7 : (same_outside_range l1_2 l1_3 left_pre (retval - 1))) (PreH8 : (range_nondecreasing l1_3 left_pre (retval - 1))) (PreH9 : (retval > left_pre)) (PreH10 : (left_pre <= retval)) (PreH11 : (retval <= right_pre)) (PreH12 : (Permutation l l1_2)) (PreH13 : (same_outside_range l l1_2 left_pre right_pre)) (PreH14 : (partitioned_at l1_2 left_pre right_pre retval)) (PreH15 : (left_pre < right_pre)) (PreH16 : ((0 : Int) <= n_pre)) (PreH17 : ((0 : Int) <= left_pre)) (PreH18 : ((-1) <= right_pre)) (PreH19 : (right_pre < n_pre)) ,
  (Permutation l l1_4)

noncomputable def quicksort_range_return_wit_2 : Prop :=
  (
forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (l1_2 : (List Int)) (retval : Int) (l1_3 : (List Int)) (PreH1 : (Permutation l1_2 l1_3)) (PreH2 : (same_outside_range l1_2 l1_3 (retval + 1) right_pre)) (PreH3 : (range_nondecreasing l1_3 (retval + 1) right_pre)) (PreH4 : (retval < right_pre)) (PreH5 : (retval <= left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (Permutation l l1_2)) (PreH9 : (same_outside_range l l1_2 left_pre right_pre)) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval)) (PreH11 : (left_pre < right_pre)) (PreH12 : ((0 : Int) <= n_pre)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
  (intArray.full arr_pre n_pre l1_3)
|--
  EX l1 : (List Int),
  “ (Permutation l l1) ” &&
  “ (same_outside_range l l1 left_pre right_pre) ” &&
  “ (range_nondecreasing l1 left_pre right_pre) ”
  &&  (intArray.full arr_pre n_pre l1)
) \/
(
forall (l : (List Int)) (n_pre : Int) (left_pre : Int) (right_pre : Int) (l1_2 : (List Int)) (retval : Int) (l1_3 : (List Int)) (PreH1 : ((Zlength (l1_3)) = n_pre)) (PreH2 : (Permutation l1_2 l1_3)) (PreH3 : (same_outside_range l1_2 l1_3 (retval + 1) right_pre)) (PreH4 : (range_nondecreasing l1_3 (retval + 1) right_pre)) (PreH5 : (retval < right_pre)) (PreH6 : (retval <= left_pre)) (PreH7 : (left_pre <= retval)) (PreH8 : (retval <= right_pre)) (PreH9 : (Permutation l l1_2)) (PreH10 : (same_outside_range l l1_2 left_pre right_pre)) (PreH11 : (partitioned_at l1_2 left_pre right_pre retval)) (PreH12 : (left_pre < right_pre)) (PreH13 : ((0 : Int) <= n_pre)) (PreH14 : ((0 : Int) <= left_pre)) (PreH15 : ((-1) <= right_pre)) (PreH16 : (right_pre < n_pre)) ,
  TT && emp 
|--
  “ (range_nondecreasing l1_3 left_pre right_pre) ” &&
  “ (same_outside_range l l1_3 left_pre right_pre) ” &&
  “ (Permutation l l1_3) ”
  &&  emp
)

noncomputable def quicksort_range_return_wit_2_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (left_pre : Int) (right_pre : Int) (l1_2 : (List Int)) (retval : Int) (l1_3 : (List Int)) (PreH1 : ((Zlength (l1_3)) = n_pre)) (PreH2 : (Permutation l1_2 l1_3)) (PreH3 : (same_outside_range l1_2 l1_3 (retval + 1) right_pre)) (PreH4 : (range_nondecreasing l1_3 (retval + 1) right_pre)) (PreH5 : (retval < right_pre)) (PreH6 : (retval <= left_pre)) (PreH7 : (left_pre <= retval)) (PreH8 : (retval <= right_pre)) (PreH9 : (Permutation l l1_2)) (PreH10 : (same_outside_range l l1_2 left_pre right_pre)) (PreH11 : (partitioned_at l1_2 left_pre right_pre retval)) (PreH12 : (left_pre < right_pre)) (PreH13 : ((0 : Int) <= n_pre)) (PreH14 : ((0 : Int) <= left_pre)) (PreH15 : ((-1) <= right_pre)) (PreH16 : (right_pre < n_pre)) ,
  (range_nondecreasing l1_3 left_pre right_pre)

noncomputable def quicksort_range_return_wit_2_split_goal_2 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (left_pre : Int) (right_pre : Int) (l1_2 : (List Int)) (retval : Int) (l1_3 : (List Int)) (PreH1 : ((Zlength (l1_3)) = n_pre)) (PreH2 : (Permutation l1_2 l1_3)) (PreH3 : (same_outside_range l1_2 l1_3 (retval + 1) right_pre)) (PreH4 : (range_nondecreasing l1_3 (retval + 1) right_pre)) (PreH5 : (retval < right_pre)) (PreH6 : (retval <= left_pre)) (PreH7 : (left_pre <= retval)) (PreH8 : (retval <= right_pre)) (PreH9 : (Permutation l l1_2)) (PreH10 : (same_outside_range l l1_2 left_pre right_pre)) (PreH11 : (partitioned_at l1_2 left_pre right_pre retval)) (PreH12 : (left_pre < right_pre)) (PreH13 : ((0 : Int) <= n_pre)) (PreH14 : ((0 : Int) <= left_pre)) (PreH15 : ((-1) <= right_pre)) (PreH16 : (right_pre < n_pre)) ,
  (same_outside_range l l1_3 left_pre right_pre)

noncomputable def quicksort_range_return_wit_2_split_goal_3 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (left_pre : Int) (right_pre : Int) (l1_2 : (List Int)) (retval : Int) (l1_3 : (List Int)) (PreH1 : ((Zlength (l1_3)) = n_pre)) (PreH2 : (Permutation l1_2 l1_3)) (PreH3 : (same_outside_range l1_2 l1_3 (retval + 1) right_pre)) (PreH4 : (range_nondecreasing l1_3 (retval + 1) right_pre)) (PreH5 : (retval < right_pre)) (PreH6 : (retval <= left_pre)) (PreH7 : (left_pre <= retval)) (PreH8 : (retval <= right_pre)) (PreH9 : (Permutation l l1_2)) (PreH10 : (same_outside_range l l1_2 left_pre right_pre)) (PreH11 : (partitioned_at l1_2 left_pre right_pre retval)) (PreH12 : (left_pre < right_pre)) (PreH13 : ((0 : Int) <= n_pre)) (PreH14 : ((0 : Int) <= left_pre)) (PreH15 : ((-1) <= right_pre)) (PreH16 : (right_pre < n_pre)) ,
  (Permutation l l1_3)

noncomputable def quicksort_range_return_wit_3 : Prop :=
  (
forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (l1_2 : (List Int)) (retval : Int) (l1_3 : (List Int)) (PreH1 : (retval >= right_pre)) (PreH2 : (Permutation l1_2 l1_3)) (PreH3 : (same_outside_range l1_2 l1_3 left_pre (retval - 1))) (PreH4 : (range_nondecreasing l1_3 left_pre (retval - 1))) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (Permutation l l1_2)) (PreH9 : (same_outside_range l l1_2 left_pre right_pre)) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval)) (PreH11 : (left_pre < right_pre)) (PreH12 : ((0 : Int) <= n_pre)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
  (intArray.full arr_pre n_pre l1_3)
|--
  EX l1 : (List Int),
  “ (Permutation l l1) ” &&
  “ (same_outside_range l l1 left_pre right_pre) ” &&
  “ (range_nondecreasing l1 left_pre right_pre) ”
  &&  (intArray.full arr_pre n_pre l1)
) \/
(
forall (l : (List Int)) (n_pre : Int) (left_pre : Int) (right_pre : Int) (l1_2 : (List Int)) (retval : Int) (l1_3 : (List Int)) (PreH1 : ((Zlength (l1_3)) = n_pre)) (PreH2 : (retval >= right_pre)) (PreH3 : (Permutation l1_2 l1_3)) (PreH4 : (same_outside_range l1_2 l1_3 left_pre (retval - 1))) (PreH5 : (range_nondecreasing l1_3 left_pre (retval - 1))) (PreH6 : (retval > left_pre)) (PreH7 : (left_pre <= retval)) (PreH8 : (retval <= right_pre)) (PreH9 : (Permutation l l1_2)) (PreH10 : (same_outside_range l l1_2 left_pre right_pre)) (PreH11 : (partitioned_at l1_2 left_pre right_pre retval)) (PreH12 : (left_pre < right_pre)) (PreH13 : ((0 : Int) <= n_pre)) (PreH14 : ((0 : Int) <= left_pre)) (PreH15 : ((-1) <= right_pre)) (PreH16 : (right_pre < n_pre)) ,
  TT && emp 
|--
  “ (range_nondecreasing l1_3 left_pre right_pre) ” &&
  “ (same_outside_range l l1_3 left_pre right_pre) ” &&
  “ (Permutation l l1_3) ”
  &&  emp
)

noncomputable def quicksort_range_return_wit_3_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (left_pre : Int) (right_pre : Int) (l1_2 : (List Int)) (retval : Int) (l1_3 : (List Int)) (PreH1 : ((Zlength (l1_3)) = n_pre)) (PreH2 : (retval >= right_pre)) (PreH3 : (Permutation l1_2 l1_3)) (PreH4 : (same_outside_range l1_2 l1_3 left_pre (retval - 1))) (PreH5 : (range_nondecreasing l1_3 left_pre (retval - 1))) (PreH6 : (retval > left_pre)) (PreH7 : (left_pre <= retval)) (PreH8 : (retval <= right_pre)) (PreH9 : (Permutation l l1_2)) (PreH10 : (same_outside_range l l1_2 left_pre right_pre)) (PreH11 : (partitioned_at l1_2 left_pre right_pre retval)) (PreH12 : (left_pre < right_pre)) (PreH13 : ((0 : Int) <= n_pre)) (PreH14 : ((0 : Int) <= left_pre)) (PreH15 : ((-1) <= right_pre)) (PreH16 : (right_pre < n_pre)) ,
  (range_nondecreasing l1_3 left_pre right_pre)

noncomputable def quicksort_range_return_wit_3_split_goal_2 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (left_pre : Int) (right_pre : Int) (l1_2 : (List Int)) (retval : Int) (l1_3 : (List Int)) (PreH1 : ((Zlength (l1_3)) = n_pre)) (PreH2 : (retval >= right_pre)) (PreH3 : (Permutation l1_2 l1_3)) (PreH4 : (same_outside_range l1_2 l1_3 left_pre (retval - 1))) (PreH5 : (range_nondecreasing l1_3 left_pre (retval - 1))) (PreH6 : (retval > left_pre)) (PreH7 : (left_pre <= retval)) (PreH8 : (retval <= right_pre)) (PreH9 : (Permutation l l1_2)) (PreH10 : (same_outside_range l l1_2 left_pre right_pre)) (PreH11 : (partitioned_at l1_2 left_pre right_pre retval)) (PreH12 : (left_pre < right_pre)) (PreH13 : ((0 : Int) <= n_pre)) (PreH14 : ((0 : Int) <= left_pre)) (PreH15 : ((-1) <= right_pre)) (PreH16 : (right_pre < n_pre)) ,
  (same_outside_range l l1_3 left_pre right_pre)

noncomputable def quicksort_range_return_wit_3_split_goal_3 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (left_pre : Int) (right_pre : Int) (l1_2 : (List Int)) (retval : Int) (l1_3 : (List Int)) (PreH1 : ((Zlength (l1_3)) = n_pre)) (PreH2 : (retval >= right_pre)) (PreH3 : (Permutation l1_2 l1_3)) (PreH4 : (same_outside_range l1_2 l1_3 left_pre (retval - 1))) (PreH5 : (range_nondecreasing l1_3 left_pre (retval - 1))) (PreH6 : (retval > left_pre)) (PreH7 : (left_pre <= retval)) (PreH8 : (retval <= right_pre)) (PreH9 : (Permutation l l1_2)) (PreH10 : (same_outside_range l l1_2 left_pre right_pre)) (PreH11 : (partitioned_at l1_2 left_pre right_pre retval)) (PreH12 : (left_pre < right_pre)) (PreH13 : ((0 : Int) <= n_pre)) (PreH14 : ((0 : Int) <= left_pre)) (PreH15 : ((-1) <= right_pre)) (PreH16 : (right_pre < n_pre)) ,
  (Permutation l l1_3)

noncomputable def quicksort_range_return_wit_4 : Prop :=
  (
forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (PreH1 : (left_pre >= right_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : ((0 : Int) <= left_pre)) (PreH4 : ((-1) <= right_pre)) (PreH5 : (right_pre < n_pre)) ,
  (intArray.full arr_pre n_pre l)
|--
  EX l1 : (List Int),
  “ (Permutation l l1) ” &&
  “ (same_outside_range l l1 left_pre right_pre) ” &&
  “ (range_nondecreasing l1 left_pre right_pre) ”
  &&  (intArray.full arr_pre n_pre l1)
) \/
(
forall (l : (List Int)) (n_pre : Int) (left_pre : Int) (right_pre : Int) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : (left_pre >= right_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : ((0 : Int) <= left_pre)) (PreH5 : ((-1) <= right_pre)) (PreH6 : (right_pre < n_pre)) ,
  TT && emp 
|--
  “ (range_nondecreasing l left_pre right_pre) ” &&
  “ (same_outside_range l l left_pre right_pre) ” &&
  “ (Permutation l l) ”
  &&  emp
)

noncomputable def quicksort_range_return_wit_4_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (left_pre : Int) (right_pre : Int) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : (left_pre >= right_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : ((0 : Int) <= left_pre)) (PreH5 : ((-1) <= right_pre)) (PreH6 : (right_pre < n_pre)) ,
  (range_nondecreasing l left_pre right_pre)

noncomputable def quicksort_range_return_wit_4_split_goal_2 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (left_pre : Int) (right_pre : Int) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : (left_pre >= right_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : ((0 : Int) <= left_pre)) (PreH5 : ((-1) <= right_pre)) (PreH6 : (right_pre < n_pre)) ,
  (same_outside_range l l left_pre right_pre)

noncomputable def quicksort_range_return_wit_4_split_goal_3 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (left_pre : Int) (right_pre : Int) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : (left_pre >= right_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : ((0 : Int) <= left_pre)) (PreH5 : ((-1) <= right_pre)) (PreH6 : (right_pre < n_pre)) ,
  (Permutation l l)

noncomputable def quicksort_range_partial_solve_wit_1_pure : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (PreH1 : (left_pre < right_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : ((0 : Int) <= left_pre)) (PreH4 : ((-1) <= right_pre)) (PreH5 : (right_pre < n_pre)) ,
  ((( &( "p" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= right_pre) ” &&
  “ (right_pre < n_pre) ”

noncomputable def quicksort_range_partial_solve_wit_1_aux : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (PreH1 : (left_pre < right_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : ((0 : Int) <= left_pre)) (PreH4 : ((-1) <= right_pre)) (PreH5 : (right_pre < n_pre)) ,
  (intArray.full arr_pre n_pre l)
|--
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= right_pre) ” &&
  “ (right_pre < n_pre) ” &&
  “ (left_pre < right_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ ((-1) <= right_pre) ” &&
  “ (right_pre < n_pre) ”
  &&  (intArray.full arr_pre n_pre l)

noncomputable def quicksort_range_partial_solve_wit_1 : Prop := quicksort_range_partial_solve_wit_1_pure -> quicksort_range_partial_solve_wit_1_aux

noncomputable def quicksort_range_partial_solve_wit_2_pure : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (l1 : (List Int)) (retval : Int) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (Permutation l l1)) (PreH5 : (same_outside_range l l1 left_pre right_pre)) (PreH6 : (partitioned_at l1 left_pre right_pre retval)) (PreH7 : (left_pre < right_pre)) (PreH8 : ((0 : Int) <= n_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : ((-1) <= right_pre)) (PreH11 : (right_pre < n_pre)) ,
  (intArray.full arr_pre n_pre l1)
  ** ((( &( "p" ) )) # Int |-> (retval))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ ((-1) <= (retval - 1)) ” &&
  “ ((retval - 1) < n_pre) ”

noncomputable def quicksort_range_partial_solve_wit_2_aux : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (l1 : (List Int)) (retval : Int) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (Permutation l l1)) (PreH5 : (same_outside_range l l1 left_pre right_pre)) (PreH6 : (partitioned_at l1 left_pre right_pre retval)) (PreH7 : (left_pre < right_pre)) (PreH8 : ((0 : Int) <= n_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : ((-1) <= right_pre)) (PreH11 : (right_pre < n_pre)) ,
  (intArray.full arr_pre n_pre l1)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ ((-1) <= (retval - 1)) ” &&
  “ ((retval - 1) < n_pre) ” &&
  “ (retval > left_pre) ” &&
  “ (left_pre <= retval) ” &&
  “ (retval <= right_pre) ” &&
  “ (Permutation l l1) ” &&
  “ (same_outside_range l l1 left_pre right_pre) ” &&
  “ (partitioned_at l1 left_pre right_pre retval) ” &&
  “ (left_pre < right_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ ((-1) <= right_pre) ” &&
  “ (right_pre < n_pre) ”
  &&  (intArray.full arr_pre n_pre l1)

noncomputable def quicksort_range_partial_solve_wit_2 : Prop := quicksort_range_partial_solve_wit_2_pure -> quicksort_range_partial_solve_wit_2_aux

noncomputable def quicksort_range_partial_solve_wit_3_pure : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (l1 : (List Int)) (retval : Int) (l1_2 : (List Int)) (PreH1 : (retval < right_pre)) (PreH2 : (Permutation l1 l1_2)) (PreH3 : (same_outside_range l1 l1_2 left_pre (retval - 1))) (PreH4 : (range_nondecreasing l1_2 left_pre (retval - 1))) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (Permutation l l1)) (PreH9 : (same_outside_range l l1 left_pre right_pre)) (PreH10 : (partitioned_at l1 left_pre right_pre retval)) (PreH11 : (left_pre < right_pre)) (PreH12 : ((0 : Int) <= n_pre)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
  (intArray.full arr_pre n_pre l1_2)
  ** ((( &( "p" ) )) # Int |-> (retval))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= (retval + 1)) ” &&
  “ ((-1) <= right_pre) ” &&
  “ (right_pre < n_pre) ”

noncomputable def quicksort_range_partial_solve_wit_3_aux : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (l1 : (List Int)) (retval : Int) (l1_2 : (List Int)) (PreH1 : (retval < right_pre)) (PreH2 : (Permutation l1 l1_2)) (PreH3 : (same_outside_range l1 l1_2 left_pre (retval - 1))) (PreH4 : (range_nondecreasing l1_2 left_pre (retval - 1))) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (Permutation l l1)) (PreH9 : (same_outside_range l l1 left_pre right_pre)) (PreH10 : (partitioned_at l1 left_pre right_pre retval)) (PreH11 : (left_pre < right_pre)) (PreH12 : ((0 : Int) <= n_pre)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
  (intArray.full arr_pre n_pre l1_2)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= (retval + 1)) ” &&
  “ ((-1) <= right_pre) ” &&
  “ (right_pre < n_pre) ” &&
  “ (retval < right_pre) ” &&
  “ (Permutation l1 l1_2) ” &&
  “ (same_outside_range l1 l1_2 left_pre (retval - 1)) ” &&
  “ (range_nondecreasing l1_2 left_pre (retval - 1)) ” &&
  “ (retval > left_pre) ” &&
  “ (left_pre <= retval) ” &&
  “ (retval <= right_pre) ” &&
  “ (Permutation l l1) ” &&
  “ (same_outside_range l l1 left_pre right_pre) ” &&
  “ (partitioned_at l1 left_pre right_pre retval) ” &&
  “ (left_pre < right_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ ((-1) <= right_pre) ” &&
  “ (right_pre < n_pre) ”
  &&  (intArray.full arr_pre n_pre l1_2)

noncomputable def quicksort_range_partial_solve_wit_3 : Prop := quicksort_range_partial_solve_wit_3_pure -> quicksort_range_partial_solve_wit_3_aux

noncomputable def quicksort_range_partial_solve_wit_4_pure : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (l1 : (List Int)) (retval : Int) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (Permutation l l1)) (PreH6 : (same_outside_range l l1 left_pre right_pre)) (PreH7 : (partitioned_at l1 left_pre right_pre retval)) (PreH8 : (left_pre < right_pre)) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : ((-1) <= right_pre)) (PreH12 : (right_pre < n_pre)) ,
  (intArray.full arr_pre n_pre l1)
  ** ((( &( "p" ) )) # Int |-> (retval))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= (retval + 1)) ” &&
  “ ((-1) <= right_pre) ” &&
  “ (right_pre < n_pre) ”

noncomputable def quicksort_range_partial_solve_wit_4_aux : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (l1 : (List Int)) (retval : Int) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (Permutation l l1)) (PreH6 : (same_outside_range l l1 left_pre right_pre)) (PreH7 : (partitioned_at l1 left_pre right_pre retval)) (PreH8 : (left_pre < right_pre)) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : ((-1) <= right_pre)) (PreH12 : (right_pre < n_pre)) ,
  (intArray.full arr_pre n_pre l1)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= (retval + 1)) ” &&
  “ ((-1) <= right_pre) ” &&
  “ (right_pre < n_pre) ” &&
  “ (retval < right_pre) ” &&
  “ (retval <= left_pre) ” &&
  “ (left_pre <= retval) ” &&
  “ (retval <= right_pre) ” &&
  “ (Permutation l l1) ” &&
  “ (same_outside_range l l1 left_pre right_pre) ” &&
  “ (partitioned_at l1 left_pre right_pre retval) ” &&
  “ (left_pre < right_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ ((-1) <= right_pre) ” &&
  “ (right_pre < n_pre) ”
  &&  (intArray.full arr_pre n_pre l1)

noncomputable def quicksort_range_partial_solve_wit_4 : Prop := quicksort_range_partial_solve_wit_4_pure -> quicksort_range_partial_solve_wit_4_aux

noncomputable def quicksort_safety_wit_1 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 50000)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((n_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre - 1)) ”

noncomputable def quicksort_safety_wit_2 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 50000)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def quicksort_safety_wit_3 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 50000)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def quicksort_return_wit_1 : Prop :=
  (
forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (l1_2 : (List Int)) (PreH1 : (Permutation l l1_2)) (PreH2 : (same_outside_range l l1_2 (0 : Int) (n_pre - 1))) (PreH3 : (range_nondecreasing l1_2 (0 : Int) (n_pre - 1))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) ,
  (intArray.full arr_pre n_pre l1_2)
|--
  EX l1 : (List Int),
  “ (Permutation l l1) ” &&
  “ (increasing l1) ”
  &&  (intArray.full arr_pre n_pre l1)
) \/
(
forall (l : (List Int)) (n_pre : Int) (l1_2 : (List Int)) (PreH1 : ((Zlength (l1_2)) = n_pre)) (PreH2 : (Permutation l l1_2)) (PreH3 : (same_outside_range l l1_2 (0 : Int) (n_pre - 1))) (PreH4 : (range_nondecreasing l1_2 (0 : Int) (n_pre - 1))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 50000)) ,
  TT && emp 
|--
  “ (increasing l1_2) ”
  &&  emp
)

noncomputable def quicksort_return_wit_1_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (l1_2 : (List Int)) (PreH1 : ((Zlength (l1_2)) = n_pre)) (PreH2 : (Permutation l l1_2)) (PreH3 : (same_outside_range l l1_2 (0 : Int) (n_pre - 1))) (PreH4 : (range_nondecreasing l1_2 (0 : Int) (n_pre - 1))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 50000)) ,
  (increasing l1_2)

noncomputable def quicksort_partial_solve_wit_1_pure : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 50000)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((-1) <= (n_pre - 1)) ” &&
  “ ((n_pre - 1) < n_pre) ”

noncomputable def quicksort_partial_solve_wit_1_aux : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 50000)) ,
  (intArray.full arr_pre n_pre l)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((-1) <= (n_pre - 1)) ” &&
  “ ((n_pre - 1) < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 50000) ”
  &&  (intArray.full arr_pre n_pre l)

noncomputable def quicksort_partial_solve_wit_1 : Prop := quicksort_partial_solve_wit_1_pure -> quicksort_partial_solve_wit_1_aux


structure VC_Correct : Type where
  proof_of_swap_return_wit_1 : swap_return_wit_1
  proof_of_swap_partial_solve_wit_1 : swap_partial_solve_wit_1
  proof_of_swap_partial_solve_wit_2 : swap_partial_solve_wit_2
  proof_of_swap_partial_solve_wit_3 : swap_partial_solve_wit_3
  proof_of_swap_partial_solve_wit_4 : swap_partial_solve_wit_4
  proof_of_partition_safety_wit_1 : partition_safety_wit_1
  proof_of_partition_safety_wit_2 : partition_safety_wit_2
  proof_of_partition_safety_wit_3 : partition_safety_wit_3
  proof_of_partition_safety_wit_4 : partition_safety_wit_4
  proof_of_partition_safety_wit_5 : partition_safety_wit_5
  proof_of_partition_safety_wit_6 : partition_safety_wit_6
  proof_of_partition_safety_wit_7 : partition_safety_wit_7
  proof_of_partition_safety_wit_8 : partition_safety_wit_8
  proof_of_partition_safety_wit_9 : partition_safety_wit_9
  proof_of_partition_partial_solve_wit_1 : partition_partial_solve_wit_1
  proof_of_partition_partial_solve_wit_2 : partition_partial_solve_wit_2
  proof_of_partition_partial_solve_wit_3_pure : partition_partial_solve_wit_3_pure
  proof_of_partition_partial_solve_wit_3 : partition_partial_solve_wit_3
  proof_of_partition_partial_solve_wit_4_pure : partition_partial_solve_wit_4_pure
  proof_of_partition_partial_solve_wit_4 : partition_partial_solve_wit_4
  proof_of_quicksort_range_safety_wit_1 : quicksort_range_safety_wit_1
  proof_of_quicksort_range_safety_wit_2 : quicksort_range_safety_wit_2
  proof_of_quicksort_range_safety_wit_3 : quicksort_range_safety_wit_3
  proof_of_quicksort_range_safety_wit_4 : quicksort_range_safety_wit_4
  proof_of_quicksort_range_safety_wit_5 : quicksort_range_safety_wit_5
  proof_of_quicksort_range_safety_wit_6 : quicksort_range_safety_wit_6
  proof_of_quicksort_range_safety_wit_7 : quicksort_range_safety_wit_7
  proof_of_quicksort_range_partial_solve_wit_1_pure : quicksort_range_partial_solve_wit_1_pure
  proof_of_quicksort_range_partial_solve_wit_1 : quicksort_range_partial_solve_wit_1
  proof_of_quicksort_range_partial_solve_wit_2_pure : quicksort_range_partial_solve_wit_2_pure
  proof_of_quicksort_range_partial_solve_wit_2 : quicksort_range_partial_solve_wit_2
  proof_of_quicksort_range_partial_solve_wit_3_pure : quicksort_range_partial_solve_wit_3_pure
  proof_of_quicksort_range_partial_solve_wit_3 : quicksort_range_partial_solve_wit_3
  proof_of_quicksort_range_partial_solve_wit_4_pure : quicksort_range_partial_solve_wit_4_pure
  proof_of_quicksort_range_partial_solve_wit_4 : quicksort_range_partial_solve_wit_4
  proof_of_quicksort_safety_wit_1 : quicksort_safety_wit_1
  proof_of_quicksort_safety_wit_2 : quicksort_safety_wit_2
  proof_of_quicksort_safety_wit_3 : quicksort_safety_wit_3
  proof_of_quicksort_partial_solve_wit_1_pure : quicksort_partial_solve_wit_1_pure
  proof_of_quicksort_partial_solve_wit_1 : quicksort_partial_solve_wit_1
  proof_of_partition_entail_wit_1 : partition_entail_wit_1
  proof_of_partition_entail_wit_2_1 : partition_entail_wit_2_1
  proof_of_partition_entail_wit_2_2 : partition_entail_wit_2_2
  proof_of_partition_return_wit_1 : partition_return_wit_1
  proof_of_quicksort_range_return_wit_1 : quicksort_range_return_wit_1
  proof_of_quicksort_range_return_wit_2 : quicksort_range_return_wit_2
  proof_of_quicksort_range_return_wit_3 : quicksort_range_return_wit_3
  proof_of_quicksort_range_return_wit_4 : quicksort_range_return_wit_4
  proof_of_quicksort_return_wit_1 : quicksort_return_wit_1

end SimpleC.EE.LLM_bench.Algorithms.quicksort_lomuto_index.quicksort_goal
