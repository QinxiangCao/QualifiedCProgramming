import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.discretize.discretize_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.discretize.discretize_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance discretize_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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
  forall (j_pre : Int) (i_pre : Int) (arr_pre : Int) (l : (List Int)) (n : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n)) ,
  (intArray.full arr_pre n (replace_Znth (j_pre) ((Znth i_pre l (0 : Int))) ((replace_Znth (i_pre) ((Znth j_pre l (0 : Int))) (l)))))
|--
  (intArray.full arr_pre n (replace_Znth (j_pre) ((Znth (i_pre) (l) ((0 : Int)))) ((replace_Znth (i_pre) ((Znth (j_pre) (l) ((0 : Int)))) (l)))))

noncomputable def swap_partial_solve_wit_1 : Prop :=
  forall (j_pre : Int) (i_pre : Int) (arr_pre : Int) (l : (List Int)) (n : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n)) ,
  (intArray.full arr_pre n l)
|--
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < n) ” &&
  “ ((0 : Int) <= j_pre) ” &&
  “ (j_pre < n) ”
  &&  (((arr_pre + (i_pre * sizeof(INT)))) # Int |-> ((Znth i_pre l (0 : Int))))
  ** (intArray.missing_i arr_pre i_pre (0 : Int) n l)

noncomputable def swap_partial_solve_wit_2 : Prop :=
  forall (j_pre : Int) (i_pre : Int) (arr_pre : Int) (l : (List Int)) (n : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n)) ,
  (intArray.full arr_pre n l)
|--
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < n) ” &&
  “ ((0 : Int) <= j_pre) ” &&
  “ (j_pre < n) ”
  &&  (((arr_pre + (j_pre * sizeof(INT)))) # Int |-> ((Znth j_pre l (0 : Int))))
  ** (intArray.missing_i arr_pre j_pre (0 : Int) n l)

noncomputable def swap_partial_solve_wit_3 : Prop :=
  forall (j_pre : Int) (i_pre : Int) (arr_pre : Int) (l : (List Int)) (n : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n)) ,
  (intArray.full arr_pre n l)
|--
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < n) ” &&
  “ ((0 : Int) <= j_pre) ” &&
  “ (j_pre < n) ”
  &&  (((arr_pre + (i_pre * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i arr_pre i_pre (0 : Int) n l)

noncomputable def swap_partial_solve_wit_4 : Prop :=
  forall (j_pre : Int) (i_pre : Int) (arr_pre : Int) (l : (List Int)) (n : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n)) ,
  (intArray.full arr_pre n (replace_Znth (i_pre) ((Znth j_pre l (0 : Int))) (l)))
|--
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < n) ” &&
  “ ((0 : Int) <= j_pre) ” &&
  “ (j_pre < n) ”
  &&  (((arr_pre + (j_pre * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i arr_pre j_pre (0 : Int) n (replace_Znth (i_pre) ((Znth j_pre l (0 : Int))) (l)))

noncomputable def partition_safety_wit_1 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) ,
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
  forall (high_pre : Int) (low_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) ,
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
  forall (high_pre : Int) (low_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (l1 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : ((Znth j l1 (0 : Int)) <= pivot)) (PreH2 : (j < high_pre)) (PreH3 : (pivot = (Znth (high_pre) (l) ((0 : Int))))) (PreH4 : ((0 : Int) <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (partition_scan_inv l l1 low_pre high_pre pivot i j)) ,
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
  forall (high_pre : Int) (low_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (l1 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : ((Znth j l1 (0 : Int)) <= pivot)) (PreH2 : (j < high_pre)) (PreH3 : (pivot = (Znth (high_pre) (l) ((0 : Int))))) (PreH4 : ((0 : Int) <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (partition_scan_inv l l1 low_pre high_pre pivot i j)) ,
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
  forall (high_pre : Int) (low_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (l1 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : ((Znth j l1 (0 : Int)) > pivot)) (PreH2 : (j < high_pre)) (PreH3 : (pivot = (Znth (high_pre) (l) ((0 : Int))))) (PreH4 : ((0 : Int) <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (partition_scan_inv l l1 low_pre high_pre pivot i j)) ,
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
  forall (high_pre : Int) (low_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (l1 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : (j >= high_pre)) (PreH2 : (pivot = (Znth (high_pre) (l) ((0 : Int))))) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (partition_scan_inv l l1 low_pre high_pre pivot i j)) ,
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
  forall (high_pre : Int) (low_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (l1 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : (j >= high_pre)) (PreH2 : (pivot = (Znth (high_pre) (l) ((0 : Int))))) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (partition_scan_inv l l1 low_pre high_pre pivot i j)) ,
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
  forall (high_pre : Int) (low_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (l1 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : (j >= high_pre)) (PreH2 : (pivot = (Znth (high_pre) (l) ((0 : Int))))) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (partition_scan_inv l l1 low_pre high_pre pivot i j)) ,
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
  forall (high_pre : Int) (low_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (l1 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : (j >= high_pre)) (PreH2 : (pivot = (Znth (high_pre) (l) ((0 : Int))))) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (partition_scan_inv l l1 low_pre high_pre pivot i j)) ,
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
forall (high_pre : Int) (low_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) ,
  (intArray.full arr_pre n_pre l)
|--
  EX l1 : (List Int),
  “ ((Znth high_pre l (0 : Int)) = (Znth (high_pre) (l) ((0 : Int)))) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ (high_pre < n_pre) ” &&
  “ ((low_pre - 1) <= (low_pre - 1)) ” &&
  “ ((low_pre - 1) < low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ (partition_scan_inv l l1 low_pre high_pre (Znth high_pre l (0 : Int)) (low_pre - 1) low_pre) ”
  &&  (intArray.full arr_pre n_pre l1)
) \/
(
forall (high_pre : Int) (low_pre : Int) (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) ,
  TT && emp 
|--
  “ (partition_scan_inv l l low_pre high_pre (Znth high_pre l (0 : Int)) (low_pre - 1) low_pre) ”
  &&  emp
)

noncomputable def partition_entail_wit_1_split_goal_1 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (n_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) ,
  (partition_scan_inv l l low_pre high_pre (Znth high_pre l (0 : Int)) (low_pre - 1) low_pre)

noncomputable def partition_entail_wit_2_1 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (l1_2 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : ((Znth j l1_2 (0 : Int)) <= pivot)) (PreH2 : (j < high_pre)) (PreH3 : (pivot = (Znth (high_pre) (l) ((0 : Int))))) (PreH4 : ((0 : Int) <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (partition_scan_inv l l1_2 low_pre high_pre pivot i j)) ,
  (intArray.full arr_pre n_pre (replace_Znth (j) ((Znth ((i + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i + 1)) ((Znth (j) (l1_2) ((0 : Int)))) (l1_2)))))
|--
  EX l1 : (List Int),
  “ (pivot = (Znth (high_pre) (l) ((0 : Int)))) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ (high_pre < n_pre) ” &&
  “ ((low_pre - 1) <= (i + 1)) ” &&
  “ ((i + 1) < (j + 1)) ” &&
  “ ((j + 1) <= high_pre) ” &&
  “ (partition_scan_inv l l1 low_pre high_pre pivot (i + 1) (j + 1)) ”
  &&  (intArray.full arr_pre n_pre l1)
) \/
(
forall (high_pre : Int) (low_pre : Int) (n_pre : Int) (l : (List Int)) (l1_2 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : ((Znth j l1_2 (0 : Int)) <= pivot)) (PreH2 : (j < high_pre)) (PreH3 : (pivot = (Znth (high_pre) (l) ((0 : Int))))) (PreH4 : ((0 : Int) <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (partition_scan_inv l l1_2 low_pre high_pre pivot i j)) ,
  TT && emp 
|--
  “ (partition_scan_inv l (replace_Znth (j) ((Znth ((i + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i + 1)) ((Znth (j) (l1_2) ((0 : Int)))) (l1_2)))) low_pre high_pre pivot (i + 1) (j + 1)) ”
  &&  emp
)

noncomputable def partition_entail_wit_2_1_split_goal_1 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (n_pre : Int) (l : (List Int)) (l1_2 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : ((Znth j l1_2 (0 : Int)) <= pivot)) (PreH2 : (j < high_pre)) (PreH3 : (pivot = (Znth (high_pre) (l) ((0 : Int))))) (PreH4 : ((0 : Int) <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (partition_scan_inv l l1_2 low_pre high_pre pivot i j)) ,
  (partition_scan_inv l (replace_Znth (j) ((Znth ((i + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i + 1)) ((Znth (j) (l1_2) ((0 : Int)))) (l1_2)))) low_pre high_pre pivot (i + 1) (j + 1))

noncomputable def partition_entail_wit_2_2 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (l1_2 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : ((Znth j l1_2 (0 : Int)) > pivot)) (PreH2 : (j < high_pre)) (PreH3 : (pivot = (Znth (high_pre) (l) ((0 : Int))))) (PreH4 : ((0 : Int) <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (partition_scan_inv l l1_2 low_pre high_pre pivot i j)) ,
  (intArray.full arr_pre n_pre l1_2)
|--
  EX l1 : (List Int),
  “ (pivot = (Znth (high_pre) (l) ((0 : Int)))) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ (high_pre < n_pre) ” &&
  “ ((low_pre - 1) <= i) ” &&
  “ (i < (j + 1)) ” &&
  “ ((j + 1) <= high_pre) ” &&
  “ (partition_scan_inv l l1 low_pre high_pre pivot i (j + 1)) ”
  &&  (intArray.full arr_pre n_pre l1)
) \/
(
forall (high_pre : Int) (low_pre : Int) (n_pre : Int) (l : (List Int)) (l1_2 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : ((Znth j l1_2 (0 : Int)) > pivot)) (PreH2 : (j < high_pre)) (PreH3 : (pivot = (Znth (high_pre) (l) ((0 : Int))))) (PreH4 : ((0 : Int) <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (partition_scan_inv l l1_2 low_pre high_pre pivot i j)) ,
  TT && emp 
|--
  “ (partition_scan_inv l l1_2 low_pre high_pre pivot i (j + 1)) ”
  &&  emp
)

noncomputable def partition_entail_wit_2_2_split_goal_1 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (n_pre : Int) (l : (List Int)) (l1_2 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : ((Znth j l1_2 (0 : Int)) > pivot)) (PreH2 : (j < high_pre)) (PreH3 : (pivot = (Znth (high_pre) (l) ((0 : Int))))) (PreH4 : ((0 : Int) <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (partition_scan_inv l l1_2 low_pre high_pre pivot i j)) ,
  (partition_scan_inv l l1_2 low_pre high_pre pivot i (j + 1))

noncomputable def partition_return_wit_1 : Prop :=
  (
forall (high_pre : Int) (low_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (l1_2 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : (j >= high_pre)) (PreH2 : (pivot = (Znth (high_pre) (l) ((0 : Int))))) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (partition_scan_inv l l1_2 low_pre high_pre pivot i j)) ,
  (intArray.full arr_pre n_pre (replace_Znth (high_pre) ((Znth ((i + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i + 1)) ((Znth (high_pre) (l1_2) ((0 : Int)))) (l1_2)))))
|--
  EX l1 : (List Int),
  “ (low_pre <= (i + 1)) ” &&
  “ ((i + 1) <= high_pre) ” &&
  “ (permutation l l1) ” &&
  “ (same_outside_range l l1 low_pre high_pre) ” &&
  “ (partitioned_at l1 low_pre high_pre (i + 1)) ”
  &&  (intArray.full arr_pre n_pre l1)
) \/
(
forall (high_pre : Int) (low_pre : Int) (n_pre : Int) (l : (List Int)) (l1_2 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : (j >= high_pre)) (PreH2 : (pivot = (Znth (high_pre) (l) ((0 : Int))))) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (partition_scan_inv l l1_2 low_pre high_pre pivot i j)) ,
  TT && emp 
|--
  “ (partitioned_at (replace_Znth (high_pre) ((Znth ((i + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i + 1)) ((Znth (high_pre) (l1_2) ((0 : Int)))) (l1_2)))) low_pre high_pre (i + 1)) ” &&
  “ (same_outside_range l (replace_Znth (high_pre) ((Znth ((i + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i + 1)) ((Znth (high_pre) (l1_2) ((0 : Int)))) (l1_2)))) low_pre high_pre) ” &&
  “ (permutation l (replace_Znth (high_pre) ((Znth ((i + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i + 1)) ((Znth (high_pre) (l1_2) ((0 : Int)))) (l1_2))))) ”
  &&  emp
)

noncomputable def partition_return_wit_1_split_goal_1 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (n_pre : Int) (l : (List Int)) (l1_2 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : (j >= high_pre)) (PreH2 : (pivot = (Znth (high_pre) (l) ((0 : Int))))) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (partition_scan_inv l l1_2 low_pre high_pre pivot i j)) ,
  (partitioned_at (replace_Znth (high_pre) ((Znth ((i + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i + 1)) ((Znth (high_pre) (l1_2) ((0 : Int)))) (l1_2)))) low_pre high_pre (i + 1))

noncomputable def partition_return_wit_1_split_goal_2 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (n_pre : Int) (l : (List Int)) (l1_2 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : (j >= high_pre)) (PreH2 : (pivot = (Znth (high_pre) (l) ((0 : Int))))) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (partition_scan_inv l l1_2 low_pre high_pre pivot i j)) ,
  (same_outside_range l (replace_Znth (high_pre) ((Znth ((i + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i + 1)) ((Znth (high_pre) (l1_2) ((0 : Int)))) (l1_2)))) low_pre high_pre)

noncomputable def partition_return_wit_1_split_goal_3 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (n_pre : Int) (l : (List Int)) (l1_2 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : (j >= high_pre)) (PreH2 : (pivot = (Znth (high_pre) (l) ((0 : Int))))) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (partition_scan_inv l l1_2 low_pre high_pre pivot i j)) ,
  (permutation l (replace_Znth (high_pre) ((Znth ((i + 1)) (l1_2) ((0 : Int)))) ((replace_Znth ((i + 1)) ((Znth (high_pre) (l1_2) ((0 : Int)))) (l1_2)))))

noncomputable def partition_partial_solve_wit_1 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : ((0 : Int) <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) ,
  (intArray.full arr_pre n_pre l)
|--
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ (high_pre < n_pre) ”
  &&  (((arr_pre + (high_pre * sizeof(INT)))) # Int |-> ((Znth high_pre l (0 : Int))))
  ** (intArray.missing_i arr_pre high_pre (0 : Int) n_pre l)

noncomputable def partition_partial_solve_wit_2 : Prop :=
  forall (high_pre : Int) (low_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (l1 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : (j < high_pre)) (PreH2 : (pivot = (Znth (high_pre) (l) ((0 : Int))))) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (partition_scan_inv l l1 low_pre high_pre pivot i j)) ,
  (intArray.full arr_pre n_pre l1)
|--
  “ (j < high_pre) ” &&
  “ (pivot = (Znth (high_pre) (l) ((0 : Int)))) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ (high_pre < n_pre) ” &&
  “ ((low_pre - 1) <= i) ” &&
  “ (i < j) ” &&
  “ (j <= high_pre) ” &&
  “ (partition_scan_inv l l1 low_pre high_pre pivot i j) ”
  &&  (((arr_pre + (j * sizeof(INT)))) # Int |-> ((Znth j l1 (0 : Int))))
  ** (intArray.missing_i arr_pre j (0 : Int) n_pre l1)

noncomputable def partition_partial_solve_wit_3_pure : Prop :=
  forall (high_pre : Int) (low_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (l1 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : ((Znth j l1 (0 : Int)) <= pivot)) (PreH2 : (j < high_pre)) (PreH3 : (pivot = (Znth (high_pre) (l) ((0 : Int))))) (PreH4 : ((0 : Int) <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (partition_scan_inv l l1 low_pre high_pre pivot i j)) ,
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
  forall (high_pre : Int) (low_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (l1 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : ((Znth j l1 (0 : Int)) <= pivot)) (PreH2 : (j < high_pre)) (PreH3 : (pivot = (Znth (high_pre) (l) ((0 : Int))))) (PreH4 : ((0 : Int) <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (partition_scan_inv l l1 low_pre high_pre pivot i j)) ,
  (intArray.full arr_pre n_pre l1)
|--
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) < n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < n_pre) ” &&
  “ ((Znth j l1 (0 : Int)) <= pivot) ” &&
  “ (j < high_pre) ” &&
  “ (pivot = (Znth (high_pre) (l) ((0 : Int)))) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ (high_pre < n_pre) ” &&
  “ ((low_pre - 1) <= i) ” &&
  “ (i < j) ” &&
  “ (j <= high_pre) ” &&
  “ (partition_scan_inv l l1 low_pre high_pre pivot i j) ”
  &&  (intArray.full arr_pre n_pre l1)

noncomputable def partition_partial_solve_wit_3 : Prop := partition_partial_solve_wit_3_pure -> partition_partial_solve_wit_3_aux

noncomputable def partition_partial_solve_wit_4_pure : Prop :=
  forall (high_pre : Int) (low_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (l1 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : (j >= high_pre)) (PreH2 : (pivot = (Znth (high_pre) (l) ((0 : Int))))) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (partition_scan_inv l l1 low_pre high_pre pivot i j)) ,
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
  forall (high_pre : Int) (low_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (l1 : (List Int)) (j : Int) (i : Int) (pivot : Int) (PreH1 : (j >= high_pre)) (PreH2 : (pivot = (Znth (high_pre) (l) ((0 : Int))))) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (partition_scan_inv l l1 low_pre high_pre pivot i j)) ,
  (intArray.full arr_pre n_pre l1)
|--
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) < n_pre) ” &&
  “ ((0 : Int) <= high_pre) ” &&
  “ (high_pre < n_pre) ” &&
  “ (j >= high_pre) ” &&
  “ (pivot = (Znth (high_pre) (l) ((0 : Int)))) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ (high_pre < n_pre) ” &&
  “ ((low_pre - 1) <= i) ” &&
  “ (i < j) ” &&
  “ (j <= high_pre) ” &&
  “ (partition_scan_inv l l1 low_pre high_pre pivot i j) ”
  &&  (intArray.full arr_pre n_pre l1)

noncomputable def partition_partial_solve_wit_4 : Prop := partition_partial_solve_wit_4_pure -> partition_partial_solve_wit_4_aux

noncomputable def quicksort_range_safety_wit_1 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (l1 : (List Int)) (retval : Int) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (permutation l l1)) (PreH5 : (same_outside_range l l1 left_pre right_pre)) (PreH6 : (partitioned_at l1 left_pre right_pre retval)) (PreH7 : (left_pre < right_pre)) (PreH8 : ((0 : Int) <= n_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : ((-1) <= right_pre)) (PreH11 : (right_pre < n_pre)) ,
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
  forall (right_pre : Int) (left_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (l1 : (List Int)) (retval : Int) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (permutation l l1)) (PreH5 : (same_outside_range l l1 left_pre right_pre)) (PreH6 : (partitioned_at l1 left_pre right_pre retval)) (PreH7 : (left_pre < right_pre)) (PreH8 : ((0 : Int) <= n_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : ((-1) <= right_pre)) (PreH11 : (right_pre < n_pre)) ,
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
  forall (right_pre : Int) (left_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (l1 : (List Int)) (retval : Int) (PreH1 : (retval >= right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (permutation l l1)) (PreH6 : (same_outside_range l l1 left_pre right_pre)) (PreH7 : (partitioned_at l1 left_pre right_pre retval)) (PreH8 : (left_pre < right_pre)) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : ((-1) <= right_pre)) (PreH12 : (right_pre < n_pre)) ,
  (intArray.full arr_pre n_pre l1)
  ** ((( &( "p" ) )) # Int |-> (retval))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ False ”

noncomputable def quicksort_range_safety_wit_4 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (l1 : (List Int)) (retval : Int) (l1_2 : (List Int)) (PreH1 : (retval < right_pre)) (PreH2 : (permutation l1 l1_2)) (PreH3 : (same_outside_range l1 l1_2 left_pre (retval - 1))) (PreH4 : (sorted_range l1_2 left_pre (retval - 1))) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (permutation l l1)) (PreH9 : (same_outside_range l l1 left_pre right_pre)) (PreH10 : (partitioned_at l1 left_pre right_pre retval)) (PreH11 : (left_pre < right_pre)) (PreH12 : ((0 : Int) <= n_pre)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
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
  forall (right_pre : Int) (left_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (l1 : (List Int)) (retval : Int) (l1_2 : (List Int)) (PreH1 : (retval < right_pre)) (PreH2 : (permutation l1 l1_2)) (PreH3 : (same_outside_range l1 l1_2 left_pre (retval - 1))) (PreH4 : (sorted_range l1_2 left_pre (retval - 1))) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (permutation l l1)) (PreH9 : (same_outside_range l l1 left_pre right_pre)) (PreH10 : (partitioned_at l1 left_pre right_pre retval)) (PreH11 : (left_pre < right_pre)) (PreH12 : ((0 : Int) <= n_pre)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
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
  forall (right_pre : Int) (left_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (l1 : (List Int)) (retval : Int) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (permutation l l1)) (PreH6 : (same_outside_range l l1 left_pre right_pre)) (PreH7 : (partitioned_at l1 left_pre right_pre retval)) (PreH8 : (left_pre < right_pre)) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : ((-1) <= right_pre)) (PreH12 : (right_pre < n_pre)) ,
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
  forall (right_pre : Int) (left_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (l1 : (List Int)) (retval : Int) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (permutation l l1)) (PreH6 : (same_outside_range l l1 left_pre right_pre)) (PreH7 : (partitioned_at l1 left_pre right_pre retval)) (PreH8 : (left_pre < right_pre)) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : ((-1) <= right_pre)) (PreH12 : (right_pre < n_pre)) ,
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
forall (right_pre : Int) (left_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (l1_2 : (List Int)) (retval : Int) (l1_3 : (List Int)) (l1_4 : (List Int)) (PreH1 : (permutation l1_3 l1_4)) (PreH2 : (same_outside_range l1_3 l1_4 (retval + 1) right_pre)) (PreH3 : (sorted_range l1_4 (retval + 1) right_pre)) (PreH4 : (retval < right_pre)) (PreH5 : (permutation l1_2 l1_3)) (PreH6 : (same_outside_range l1_2 l1_3 left_pre (retval - 1))) (PreH7 : (sorted_range l1_3 left_pre (retval - 1))) (PreH8 : (retval > left_pre)) (PreH9 : (left_pre <= retval)) (PreH10 : (retval <= right_pre)) (PreH11 : (permutation l l1_2)) (PreH12 : (same_outside_range l l1_2 left_pre right_pre)) (PreH13 : (partitioned_at l1_2 left_pre right_pre retval)) (PreH14 : (left_pre < right_pre)) (PreH15 : ((0 : Int) <= n_pre)) (PreH16 : ((0 : Int) <= left_pre)) (PreH17 : ((-1) <= right_pre)) (PreH18 : (right_pre < n_pre)) ,
  (intArray.full arr_pre n_pre l1_4)
|--
  EX l1 : (List Int),
  “ (permutation l l1) ” &&
  “ (same_outside_range l l1 left_pre right_pre) ” &&
  “ (sorted_range l1 left_pre right_pre) ”
  &&  (intArray.full arr_pre n_pre l1)
) \/
(
forall (right_pre : Int) (left_pre : Int) (n_pre : Int) (l : (List Int)) (l1_2 : (List Int)) (retval : Int) (l1_3 : (List Int)) (l1_4 : (List Int)) (PreH1 : (permutation l1_3 l1_4)) (PreH2 : (same_outside_range l1_3 l1_4 (retval + 1) right_pre)) (PreH3 : (sorted_range l1_4 (retval + 1) right_pre)) (PreH4 : (retval < right_pre)) (PreH5 : (permutation l1_2 l1_3)) (PreH6 : (same_outside_range l1_2 l1_3 left_pre (retval - 1))) (PreH7 : (sorted_range l1_3 left_pre (retval - 1))) (PreH8 : (retval > left_pre)) (PreH9 : (left_pre <= retval)) (PreH10 : (retval <= right_pre)) (PreH11 : (permutation l l1_2)) (PreH12 : (same_outside_range l l1_2 left_pre right_pre)) (PreH13 : (partitioned_at l1_2 left_pre right_pre retval)) (PreH14 : (left_pre < right_pre)) (PreH15 : ((0 : Int) <= n_pre)) (PreH16 : ((0 : Int) <= left_pre)) (PreH17 : ((-1) <= right_pre)) (PreH18 : (right_pre < n_pre)) ,
  TT && emp 
|--
  “ (sorted_range l1_4 left_pre right_pre) ” &&
  “ (same_outside_range l l1_4 left_pre right_pre) ” &&
  “ (permutation l l1_4) ”
  &&  emp
)

noncomputable def quicksort_range_return_wit_1_split_goal_1 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (n_pre : Int) (l : (List Int)) (l1_2 : (List Int)) (retval : Int) (l1_3 : (List Int)) (l1_4 : (List Int)) (PreH1 : (permutation l1_3 l1_4)) (PreH2 : (same_outside_range l1_3 l1_4 (retval + 1) right_pre)) (PreH3 : (sorted_range l1_4 (retval + 1) right_pre)) (PreH4 : (retval < right_pre)) (PreH5 : (permutation l1_2 l1_3)) (PreH6 : (same_outside_range l1_2 l1_3 left_pre (retval - 1))) (PreH7 : (sorted_range l1_3 left_pre (retval - 1))) (PreH8 : (retval > left_pre)) (PreH9 : (left_pre <= retval)) (PreH10 : (retval <= right_pre)) (PreH11 : (permutation l l1_2)) (PreH12 : (same_outside_range l l1_2 left_pre right_pre)) (PreH13 : (partitioned_at l1_2 left_pre right_pre retval)) (PreH14 : (left_pre < right_pre)) (PreH15 : ((0 : Int) <= n_pre)) (PreH16 : ((0 : Int) <= left_pre)) (PreH17 : ((-1) <= right_pre)) (PreH18 : (right_pre < n_pre)) ,
  (sorted_range l1_4 left_pre right_pre)

noncomputable def quicksort_range_return_wit_1_split_goal_2 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (n_pre : Int) (l : (List Int)) (l1_2 : (List Int)) (retval : Int) (l1_3 : (List Int)) (l1_4 : (List Int)) (PreH1 : (permutation l1_3 l1_4)) (PreH2 : (same_outside_range l1_3 l1_4 (retval + 1) right_pre)) (PreH3 : (sorted_range l1_4 (retval + 1) right_pre)) (PreH4 : (retval < right_pre)) (PreH5 : (permutation l1_2 l1_3)) (PreH6 : (same_outside_range l1_2 l1_3 left_pre (retval - 1))) (PreH7 : (sorted_range l1_3 left_pre (retval - 1))) (PreH8 : (retval > left_pre)) (PreH9 : (left_pre <= retval)) (PreH10 : (retval <= right_pre)) (PreH11 : (permutation l l1_2)) (PreH12 : (same_outside_range l l1_2 left_pre right_pre)) (PreH13 : (partitioned_at l1_2 left_pre right_pre retval)) (PreH14 : (left_pre < right_pre)) (PreH15 : ((0 : Int) <= n_pre)) (PreH16 : ((0 : Int) <= left_pre)) (PreH17 : ((-1) <= right_pre)) (PreH18 : (right_pre < n_pre)) ,
  (same_outside_range l l1_4 left_pre right_pre)

noncomputable def quicksort_range_return_wit_1_split_goal_3 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (n_pre : Int) (l : (List Int)) (l1_2 : (List Int)) (retval : Int) (l1_3 : (List Int)) (l1_4 : (List Int)) (PreH1 : (permutation l1_3 l1_4)) (PreH2 : (same_outside_range l1_3 l1_4 (retval + 1) right_pre)) (PreH3 : (sorted_range l1_4 (retval + 1) right_pre)) (PreH4 : (retval < right_pre)) (PreH5 : (permutation l1_2 l1_3)) (PreH6 : (same_outside_range l1_2 l1_3 left_pre (retval - 1))) (PreH7 : (sorted_range l1_3 left_pre (retval - 1))) (PreH8 : (retval > left_pre)) (PreH9 : (left_pre <= retval)) (PreH10 : (retval <= right_pre)) (PreH11 : (permutation l l1_2)) (PreH12 : (same_outside_range l l1_2 left_pre right_pre)) (PreH13 : (partitioned_at l1_2 left_pre right_pre retval)) (PreH14 : (left_pre < right_pre)) (PreH15 : ((0 : Int) <= n_pre)) (PreH16 : ((0 : Int) <= left_pre)) (PreH17 : ((-1) <= right_pre)) (PreH18 : (right_pre < n_pre)) ,
  (permutation l l1_4)

noncomputable def quicksort_range_return_wit_2 : Prop :=
  (
forall (right_pre : Int) (left_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (l1_2 : (List Int)) (retval : Int) (l1_3 : (List Int)) (PreH1 : (permutation l1_2 l1_3)) (PreH2 : (same_outside_range l1_2 l1_3 (retval + 1) right_pre)) (PreH3 : (sorted_range l1_3 (retval + 1) right_pre)) (PreH4 : (retval < right_pre)) (PreH5 : (retval <= left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (permutation l l1_2)) (PreH9 : (same_outside_range l l1_2 left_pre right_pre)) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval)) (PreH11 : (left_pre < right_pre)) (PreH12 : ((0 : Int) <= n_pre)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
  (intArray.full arr_pre n_pre l1_3)
|--
  EX l1 : (List Int),
  “ (permutation l l1) ” &&
  “ (same_outside_range l l1 left_pre right_pre) ” &&
  “ (sorted_range l1 left_pre right_pre) ”
  &&  (intArray.full arr_pre n_pre l1)
) \/
(
forall (right_pre : Int) (left_pre : Int) (n_pre : Int) (l : (List Int)) (l1_2 : (List Int)) (retval : Int) (l1_3 : (List Int)) (PreH1 : (permutation l1_2 l1_3)) (PreH2 : (same_outside_range l1_2 l1_3 (retval + 1) right_pre)) (PreH3 : (sorted_range l1_3 (retval + 1) right_pre)) (PreH4 : (retval < right_pre)) (PreH5 : (retval <= left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (permutation l l1_2)) (PreH9 : (same_outside_range l l1_2 left_pre right_pre)) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval)) (PreH11 : (left_pre < right_pre)) (PreH12 : ((0 : Int) <= n_pre)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
  TT && emp 
|--
  “ (sorted_range l1_3 left_pre right_pre) ” &&
  “ (same_outside_range l l1_3 left_pre right_pre) ” &&
  “ (permutation l l1_3) ”
  &&  emp
)

noncomputable def quicksort_range_return_wit_2_split_goal_1 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (n_pre : Int) (l : (List Int)) (l1_2 : (List Int)) (retval : Int) (l1_3 : (List Int)) (PreH1 : (permutation l1_2 l1_3)) (PreH2 : (same_outside_range l1_2 l1_3 (retval + 1) right_pre)) (PreH3 : (sorted_range l1_3 (retval + 1) right_pre)) (PreH4 : (retval < right_pre)) (PreH5 : (retval <= left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (permutation l l1_2)) (PreH9 : (same_outside_range l l1_2 left_pre right_pre)) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval)) (PreH11 : (left_pre < right_pre)) (PreH12 : ((0 : Int) <= n_pre)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
  (sorted_range l1_3 left_pre right_pre)

noncomputable def quicksort_range_return_wit_2_split_goal_2 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (n_pre : Int) (l : (List Int)) (l1_2 : (List Int)) (retval : Int) (l1_3 : (List Int)) (PreH1 : (permutation l1_2 l1_3)) (PreH2 : (same_outside_range l1_2 l1_3 (retval + 1) right_pre)) (PreH3 : (sorted_range l1_3 (retval + 1) right_pre)) (PreH4 : (retval < right_pre)) (PreH5 : (retval <= left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (permutation l l1_2)) (PreH9 : (same_outside_range l l1_2 left_pre right_pre)) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval)) (PreH11 : (left_pre < right_pre)) (PreH12 : ((0 : Int) <= n_pre)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
  (same_outside_range l l1_3 left_pre right_pre)

noncomputable def quicksort_range_return_wit_2_split_goal_3 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (n_pre : Int) (l : (List Int)) (l1_2 : (List Int)) (retval : Int) (l1_3 : (List Int)) (PreH1 : (permutation l1_2 l1_3)) (PreH2 : (same_outside_range l1_2 l1_3 (retval + 1) right_pre)) (PreH3 : (sorted_range l1_3 (retval + 1) right_pre)) (PreH4 : (retval < right_pre)) (PreH5 : (retval <= left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (permutation l l1_2)) (PreH9 : (same_outside_range l l1_2 left_pre right_pre)) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval)) (PreH11 : (left_pre < right_pre)) (PreH12 : ((0 : Int) <= n_pre)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
  (permutation l l1_3)

noncomputable def quicksort_range_return_wit_3 : Prop :=
  (
forall (right_pre : Int) (left_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (l1_2 : (List Int)) (retval : Int) (l1_3 : (List Int)) (PreH1 : (retval >= right_pre)) (PreH2 : (permutation l1_2 l1_3)) (PreH3 : (same_outside_range l1_2 l1_3 left_pre (retval - 1))) (PreH4 : (sorted_range l1_3 left_pre (retval - 1))) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (permutation l l1_2)) (PreH9 : (same_outside_range l l1_2 left_pre right_pre)) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval)) (PreH11 : (left_pre < right_pre)) (PreH12 : ((0 : Int) <= n_pre)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
  (intArray.full arr_pre n_pre l1_3)
|--
  EX l1 : (List Int),
  “ (permutation l l1) ” &&
  “ (same_outside_range l l1 left_pre right_pre) ” &&
  “ (sorted_range l1 left_pre right_pre) ”
  &&  (intArray.full arr_pre n_pre l1)
) \/
(
forall (right_pre : Int) (left_pre : Int) (n_pre : Int) (l : (List Int)) (l1_2 : (List Int)) (retval : Int) (l1_3 : (List Int)) (PreH1 : (retval >= right_pre)) (PreH2 : (permutation l1_2 l1_3)) (PreH3 : (same_outside_range l1_2 l1_3 left_pre (retval - 1))) (PreH4 : (sorted_range l1_3 left_pre (retval - 1))) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (permutation l l1_2)) (PreH9 : (same_outside_range l l1_2 left_pre right_pre)) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval)) (PreH11 : (left_pre < right_pre)) (PreH12 : ((0 : Int) <= n_pre)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
  TT && emp 
|--
  “ (sorted_range l1_3 left_pre right_pre) ” &&
  “ (same_outside_range l l1_3 left_pre right_pre) ” &&
  “ (permutation l l1_3) ”
  &&  emp
)

noncomputable def quicksort_range_return_wit_3_split_goal_1 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (n_pre : Int) (l : (List Int)) (l1_2 : (List Int)) (retval : Int) (l1_3 : (List Int)) (PreH1 : (retval >= right_pre)) (PreH2 : (permutation l1_2 l1_3)) (PreH3 : (same_outside_range l1_2 l1_3 left_pre (retval - 1))) (PreH4 : (sorted_range l1_3 left_pre (retval - 1))) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (permutation l l1_2)) (PreH9 : (same_outside_range l l1_2 left_pre right_pre)) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval)) (PreH11 : (left_pre < right_pre)) (PreH12 : ((0 : Int) <= n_pre)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
  (sorted_range l1_3 left_pre right_pre)

noncomputable def quicksort_range_return_wit_3_split_goal_2 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (n_pre : Int) (l : (List Int)) (l1_2 : (List Int)) (retval : Int) (l1_3 : (List Int)) (PreH1 : (retval >= right_pre)) (PreH2 : (permutation l1_2 l1_3)) (PreH3 : (same_outside_range l1_2 l1_3 left_pre (retval - 1))) (PreH4 : (sorted_range l1_3 left_pre (retval - 1))) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (permutation l l1_2)) (PreH9 : (same_outside_range l l1_2 left_pre right_pre)) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval)) (PreH11 : (left_pre < right_pre)) (PreH12 : ((0 : Int) <= n_pre)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
  (same_outside_range l l1_3 left_pre right_pre)

noncomputable def quicksort_range_return_wit_3_split_goal_3 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (n_pre : Int) (l : (List Int)) (l1_2 : (List Int)) (retval : Int) (l1_3 : (List Int)) (PreH1 : (retval >= right_pre)) (PreH2 : (permutation l1_2 l1_3)) (PreH3 : (same_outside_range l1_2 l1_3 left_pre (retval - 1))) (PreH4 : (sorted_range l1_3 left_pre (retval - 1))) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (permutation l l1_2)) (PreH9 : (same_outside_range l l1_2 left_pre right_pre)) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval)) (PreH11 : (left_pre < right_pre)) (PreH12 : ((0 : Int) <= n_pre)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
  (permutation l l1_3)

noncomputable def quicksort_range_return_wit_4 : Prop :=
  (
forall (right_pre : Int) (left_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : (left_pre >= right_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : ((0 : Int) <= left_pre)) (PreH4 : ((-1) <= right_pre)) (PreH5 : (right_pre < n_pre)) ,
  (intArray.full arr_pre n_pre l)
|--
  EX l1 : (List Int),
  “ (permutation l l1) ” &&
  “ (same_outside_range l l1 left_pre right_pre) ” &&
  “ (sorted_range l1 left_pre right_pre) ”
  &&  (intArray.full arr_pre n_pre l1)
) \/
(
forall (right_pre : Int) (left_pre : Int) (n_pre : Int) (l : (List Int)) (PreH1 : (left_pre >= right_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : ((0 : Int) <= left_pre)) (PreH4 : ((-1) <= right_pre)) (PreH5 : (right_pre < n_pre)) ,
  TT && emp 
|--
  “ (sorted_range l left_pre right_pre) ” &&
  “ (same_outside_range l l left_pre right_pre) ” &&
  “ (permutation l l) ”
  &&  emp
)

noncomputable def quicksort_range_return_wit_4_split_goal_1 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (n_pre : Int) (l : (List Int)) (PreH1 : (left_pre >= right_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : ((0 : Int) <= left_pre)) (PreH4 : ((-1) <= right_pre)) (PreH5 : (right_pre < n_pre)) ,
  (sorted_range l left_pre right_pre)

noncomputable def quicksort_range_return_wit_4_split_goal_2 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (n_pre : Int) (l : (List Int)) (PreH1 : (left_pre >= right_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : ((0 : Int) <= left_pre)) (PreH4 : ((-1) <= right_pre)) (PreH5 : (right_pre < n_pre)) ,
  (same_outside_range l l left_pre right_pre)

noncomputable def quicksort_range_return_wit_4_split_goal_3 : Prop :=
  forall (right_pre : Int) (left_pre : Int) (n_pre : Int) (l : (List Int)) (PreH1 : (left_pre >= right_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : ((0 : Int) <= left_pre)) (PreH4 : ((-1) <= right_pre)) (PreH5 : (right_pre < n_pre)) ,
  (permutation l l)

noncomputable def quicksort_range_partial_solve_wit_1_pure : Prop :=
  forall (right_pre : Int) (left_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : (left_pre < right_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : ((0 : Int) <= left_pre)) (PreH4 : ((-1) <= right_pre)) (PreH5 : (right_pre < n_pre)) ,
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
  forall (right_pre : Int) (left_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : (left_pre < right_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : ((0 : Int) <= left_pre)) (PreH4 : ((-1) <= right_pre)) (PreH5 : (right_pre < n_pre)) ,
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
  forall (right_pre : Int) (left_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (l1 : (List Int)) (retval : Int) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (permutation l l1)) (PreH5 : (same_outside_range l l1 left_pre right_pre)) (PreH6 : (partitioned_at l1 left_pre right_pre retval)) (PreH7 : (left_pre < right_pre)) (PreH8 : ((0 : Int) <= n_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : ((-1) <= right_pre)) (PreH11 : (right_pre < n_pre)) ,
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
  forall (right_pre : Int) (left_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (l1 : (List Int)) (retval : Int) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (permutation l l1)) (PreH5 : (same_outside_range l l1 left_pre right_pre)) (PreH6 : (partitioned_at l1 left_pre right_pre retval)) (PreH7 : (left_pre < right_pre)) (PreH8 : ((0 : Int) <= n_pre)) (PreH9 : ((0 : Int) <= left_pre)) (PreH10 : ((-1) <= right_pre)) (PreH11 : (right_pre < n_pre)) ,
  (intArray.full arr_pre n_pre l1)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ ((-1) <= (retval - 1)) ” &&
  “ ((retval - 1) < n_pre) ” &&
  “ (retval > left_pre) ” &&
  “ (left_pre <= retval) ” &&
  “ (retval <= right_pre) ” &&
  “ (permutation l l1) ” &&
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
  forall (right_pre : Int) (left_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (l1 : (List Int)) (retval : Int) (l1_2 : (List Int)) (PreH1 : (retval < right_pre)) (PreH2 : (permutation l1 l1_2)) (PreH3 : (same_outside_range l1 l1_2 left_pre (retval - 1))) (PreH4 : (sorted_range l1_2 left_pre (retval - 1))) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (permutation l l1)) (PreH9 : (same_outside_range l l1 left_pre right_pre)) (PreH10 : (partitioned_at l1 left_pre right_pre retval)) (PreH11 : (left_pre < right_pre)) (PreH12 : ((0 : Int) <= n_pre)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
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
  forall (right_pre : Int) (left_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (l1 : (List Int)) (retval : Int) (l1_2 : (List Int)) (PreH1 : (retval < right_pre)) (PreH2 : (permutation l1 l1_2)) (PreH3 : (same_outside_range l1 l1_2 left_pre (retval - 1))) (PreH4 : (sorted_range l1_2 left_pre (retval - 1))) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (permutation l l1)) (PreH9 : (same_outside_range l l1 left_pre right_pre)) (PreH10 : (partitioned_at l1 left_pre right_pre retval)) (PreH11 : (left_pre < right_pre)) (PreH12 : ((0 : Int) <= n_pre)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
  (intArray.full arr_pre n_pre l1_2)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= (retval + 1)) ” &&
  “ ((-1) <= right_pre) ” &&
  “ (right_pre < n_pre) ” &&
  “ (retval < right_pre) ” &&
  “ (permutation l1 l1_2) ” &&
  “ (same_outside_range l1 l1_2 left_pre (retval - 1)) ” &&
  “ (sorted_range l1_2 left_pre (retval - 1)) ” &&
  “ (retval > left_pre) ” &&
  “ (left_pre <= retval) ” &&
  “ (retval <= right_pre) ” &&
  “ (permutation l l1) ” &&
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
  forall (right_pre : Int) (left_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (l1 : (List Int)) (retval : Int) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (permutation l l1)) (PreH6 : (same_outside_range l l1 left_pre right_pre)) (PreH7 : (partitioned_at l1 left_pre right_pre retval)) (PreH8 : (left_pre < right_pre)) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : ((-1) <= right_pre)) (PreH12 : (right_pre < n_pre)) ,
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
  forall (right_pre : Int) (left_pre : Int) (n_pre : Int) (arr_pre : Int) (l : (List Int)) (l1 : (List Int)) (retval : Int) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (permutation l l1)) (PreH6 : (same_outside_range l l1 left_pre right_pre)) (PreH7 : (partitioned_at l1 left_pre right_pre retval)) (PreH8 : (left_pre < right_pre)) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : ((-1) <= right_pre)) (PreH12 : (right_pre < n_pre)) ,
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
  “ (permutation l l1) ” &&
  “ (same_outside_range l l1 left_pre right_pre) ” &&
  “ (partitioned_at l1 left_pre right_pre retval) ” &&
  “ (left_pre < right_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ ((-1) <= right_pre) ” &&
  “ (right_pre < n_pre) ”
  &&  (intArray.full arr_pre n_pre l1)

noncomputable def quicksort_range_partial_solve_wit_4 : Prop := quicksort_range_partial_solve_wit_4_pure -> quicksort_range_partial_solve_wit_4_aux

noncomputable def int_array_quicksort_safety_wit_1 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 50000)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((n_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre - 1)) ”

noncomputable def int_array_quicksort_safety_wit_2 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 50000)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def int_array_quicksort_safety_wit_3 : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 50000)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def int_array_quicksort_return_wit_1 : Prop :=
  (
forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (l1_2 : (List Int)) (PreH1 : (permutation l l1_2)) (PreH2 : (same_outside_range l l1_2 (0 : Int) (n_pre - 1))) (PreH3 : (sorted_range l1_2 (0 : Int) (n_pre - 1))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) ,
  (intArray.full arr_pre n_pre l1_2)
|--
  EX l1 : (List Int),
  “ (permutation l l1) ” &&
  “ (increasing l1) ”
  &&  (intArray.full arr_pre n_pre l1)
) \/
(
forall (n_pre : Int) (l : (List Int)) (l1_2 : (List Int)) (PreH1 : (permutation l l1_2)) (PreH2 : (same_outside_range l l1_2 (0 : Int) (n_pre - 1))) (PreH3 : (sorted_range l1_2 (0 : Int) (n_pre - 1))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) ,
  TT && emp 
|--
  “ (increasing l1_2) ”
  &&  emp
)

noncomputable def int_array_quicksort_return_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (l : (List Int)) (l1_2 : (List Int)) (PreH1 : (permutation l l1_2)) (PreH2 : (same_outside_range l l1_2 (0 : Int) (n_pre - 1))) (PreH3 : (sorted_range l1_2 (0 : Int) (n_pre - 1))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) ,
  (increasing l1_2)

noncomputable def int_array_quicksort_partial_solve_wit_1_pure : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 50000)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((-1) <= (n_pre - 1)) ” &&
  “ ((n_pre - 1) < n_pre) ”

noncomputable def int_array_quicksort_partial_solve_wit_1_aux : Prop :=
  forall (n_pre : Int) (arr_pre : Int) (l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 50000)) ,
  (intArray.full arr_pre n_pre l)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((-1) <= (n_pre - 1)) ” &&
  “ ((n_pre - 1) < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 50000) ”
  &&  (intArray.full arr_pre n_pre l)

noncomputable def int_array_quicksort_partial_solve_wit_1 : Prop := int_array_quicksort_partial_solve_wit_1_pure -> int_array_quicksort_partial_solve_wit_1_aux

noncomputable def discretize_safety_wit_1 : Prop :=
  forall (dest_map_pre : Int) (n_pre : Int) (src_pre : Int) (src_l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 50000)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "src" ) )) # Ptr |-> (src_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "dest_map" ) )) # Ptr |-> (dest_map_pre))
  ** (intArray.full src_pre n_pre src_l)
  ** (intArray.undef_full dest_map_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def discretize_safety_wit_2 : Prop :=
  forall (dest_map_pre : Int) (n_pre : Int) (src_pre : Int) (src_l : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) ,
  (intArray.full dest_map_pre (i + 1) ((sublist ((0 : Int)) (i) (src_l)) ++ ((Znth i src_l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg dest_map_pre (i + 1) n_pre)
  ** (intArray.full src_pre n_pre src_l)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "src" ) )) # Ptr |-> (src_pre))
  ** ((( &( "dest_map" ) )) # Ptr |-> (dest_map_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def discretize_safety_wit_3 : Prop :=
  forall (dest_map_pre : Int) (n_pre : Int) (src_pre : Int) (src_l : (List Int)) (l1 : (List Int)) (PreH1 : (permutation src_l l1)) (PreH2 : (increasing l1)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) ,
  ((( &( "slow" ) )) # Int |->_)
  ** (intArray.full dest_map_pre n_pre l1)
  ** ((( &( "src" ) )) # Ptr |-> (src_pre))
  ** ((( &( "dest_map" ) )) # Ptr |-> (dest_map_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full src_pre n_pre src_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def discretize_safety_wit_4 : Prop :=
  forall (dest_map_pre : Int) (n_pre : Int) (src_pre : Int) (src_l : (List Int)) (l1 : (List Int)) (PreH1 : (permutation src_l l1)) (PreH2 : (increasing l1)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) ,
  ((( &( "fast" ) )) # Int |->_)
  ** ((( &( "slow" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full dest_map_pre n_pre l1)
  ** ((( &( "src" ) )) # Ptr |-> (src_pre))
  ** ((( &( "dest_map" ) )) # Ptr |-> (dest_map_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full src_pre n_pre src_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def discretize_safety_wit_5 : Prop :=
  forall (dest_map_pre : Int) (n_pre : Int) (src_pre : Int) (src_l : (List Int)) (sorted_l : (List Int)) (cur_l : (List Int)) (fast : Int) (slow : Int) (PreH1 : ((Znth fast cur_l (0 : Int)) ≠ (Znth slow cur_l (0 : Int)))) (PreH2 : (fast < n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((0 : Int) <= slow)) (PreH5 : (slow < fast)) (PreH6 : (1 <= fast)) (PreH7 : (fast <= n_pre)) (PreH8 : (dedup_scan_inv src_l sorted_l cur_l slow fast)) ,
  (intArray.full dest_map_pre n_pre cur_l)
  ** ((( &( "src" ) )) # Ptr |-> (src_pre))
  ** ((( &( "dest_map" ) )) # Ptr |-> (dest_map_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "slow" ) )) # Int |-> (slow))
  ** ((( &( "fast" ) )) # Int |-> (fast))
  ** (intArray.full src_pre n_pre src_l)
|--
  “ ((slow + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (slow + 1)) ”

noncomputable def discretize_safety_wit_6 : Prop :=
  forall (dest_map_pre : Int) (n_pre : Int) (src_pre : Int) (src_l : (List Int)) (sorted_l : (List Int)) (cur_l : (List Int)) (fast : Int) (slow : Int) (PreH1 : ((Znth fast cur_l (0 : Int)) ≠ (Znth slow cur_l (0 : Int)))) (PreH2 : (fast < n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((0 : Int) <= slow)) (PreH5 : (slow < fast)) (PreH6 : (1 <= fast)) (PreH7 : (fast <= n_pre)) (PreH8 : (dedup_scan_inv src_l sorted_l cur_l slow fast)) ,
  (intArray.full dest_map_pre n_pre (replace_Znth ((slow + 1)) ((Znth fast cur_l (0 : Int))) (cur_l)))
  ** ((( &( "src" ) )) # Ptr |-> (src_pre))
  ** ((( &( "dest_map" ) )) # Ptr |-> (dest_map_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "slow" ) )) # Int |-> ((slow + 1)))
  ** ((( &( "fast" ) )) # Int |-> (fast))
  ** (intArray.full src_pre n_pre src_l)
|--
  “ ((fast + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (fast + 1)) ”

noncomputable def discretize_safety_wit_7 : Prop :=
  forall (dest_map_pre : Int) (n_pre : Int) (src_pre : Int) (src_l : (List Int)) (sorted_l : (List Int)) (cur_l : (List Int)) (fast : Int) (slow : Int) (PreH1 : ((Znth fast cur_l (0 : Int)) = (Znth slow cur_l (0 : Int)))) (PreH2 : (fast < n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((0 : Int) <= slow)) (PreH5 : (slow < fast)) (PreH6 : (1 <= fast)) (PreH7 : (fast <= n_pre)) (PreH8 : (dedup_scan_inv src_l sorted_l cur_l slow fast)) ,
  (intArray.full dest_map_pre n_pre cur_l)
  ** ((( &( "src" ) )) # Ptr |-> (src_pre))
  ** ((( &( "dest_map" ) )) # Ptr |-> (dest_map_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "slow" ) )) # Int |-> (slow))
  ** ((( &( "fast" ) )) # Int |-> (fast))
  ** (intArray.full src_pre n_pre src_l)
|--
  “ ((fast + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (fast + 1)) ”

noncomputable def discretize_safety_wit_8 : Prop :=
  forall (dest_map_pre : Int) (n_pre : Int) (src_pre : Int) (src_l : (List Int)) (sorted_l : (List Int)) (cur_l : (List Int)) (fast : Int) (slow : Int) (PreH1 : (fast >= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((0 : Int) <= slow)) (PreH4 : (slow < fast)) (PreH5 : (1 <= fast)) (PreH6 : (fast <= n_pre)) (PreH7 : (dedup_scan_inv src_l sorted_l cur_l slow fast)) ,
  ((( &( "src" ) )) # Ptr |-> (src_pre))
  ** ((( &( "dest_map" ) )) # Ptr |-> (dest_map_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "slow" ) )) # Int |-> (slow))
  ** (intArray.full src_pre n_pre src_l)
  ** (intArray.full dest_map_pre n_pre cur_l)
|--
  “ ((slow + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (slow + 1)) ”

noncomputable def discretize_safety_wit_9 : Prop :=
  forall (dest_map_pre : Int) (n_pre : Int) (src_pre : Int) (src_l : (List Int)) (sorted_l : (List Int)) (cur_l : (List Int)) (fast : Int) (slow : Int) (PreH1 : (fast >= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((0 : Int) <= slow)) (PreH4 : (slow < fast)) (PreH5 : (1 <= fast)) (PreH6 : (fast <= n_pre)) (PreH7 : (dedup_scan_inv src_l sorted_l cur_l slow fast)) ,
  ((( &( "src" ) )) # Ptr |-> (src_pre))
  ** ((( &( "dest_map" ) )) # Ptr |-> (dest_map_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "slow" ) )) # Int |-> (slow))
  ** (intArray.full src_pre n_pre src_l)
  ** (intArray.full dest_map_pre n_pre cur_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def discretize_entail_wit_1 : Prop :=
  (
forall (dest_map_pre : Int) (n_pre : Int) (src_pre : Int) (src_l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 50000)) ,
  (intArray.full src_pre n_pre src_l)
  ** (intArray.undef_full dest_map_pre n_pre)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ”
  &&  (intArray.full src_pre n_pre src_l)
  ** (intArray.full dest_map_pre (0 : Int) (sublist ((0 : Int)) ((0 : Int)) (src_l)))
  ** (intArray.undef_seg dest_map_pre (0 : Int) n_pre)
) \/
(
forall (n_pre : Int) (src_l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 50000)) ,
  TT && emp 
|--
  “ ((sublist ((0 : Int)) ((0 : Int)) (src_l)) = (@List.nil Int)) ”
  &&  emp
)

noncomputable def discretize_entail_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (src_l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 50000)) ,
  ((sublist ((0 : Int)) ((0 : Int)) (src_l)) = (@List.nil Int))

noncomputable def discretize_entail_wit_2 : Prop :=
  (
forall (dest_map_pre : Int) (n_pre : Int) (src_pre : Int) (src_l : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) ,
  (intArray.full dest_map_pre (i + 1) ((sublist ((0 : Int)) (i) (src_l)) ++ ((Znth i src_l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg dest_map_pre (i + 1) n_pre)
  ** (intArray.full src_pre n_pre src_l)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ”
  &&  (intArray.full src_pre n_pre src_l)
  ** (intArray.full dest_map_pre (i + 1) (sublist ((0 : Int)) ((i + 1)) (src_l)))
  ** (intArray.undef_seg dest_map_pre (i + 1) n_pre)
) \/
(
forall (n_pre : Int) (src_l : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) ,
  TT && emp 
|--
  “ (((sublist ((0 : Int)) (i) (src_l)) ++ ((Znth i src_l (0 : Int)) :: (@List.nil Int))) = (sublist ((0 : Int)) ((i + 1)) (src_l))) ”
  &&  emp
)

noncomputable def discretize_entail_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (src_l : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) ,
  (((sublist ((0 : Int)) (i) (src_l)) ++ ((Znth i src_l (0 : Int)) :: (@List.nil Int))) = (sublist ((0 : Int)) ((i + 1)) (src_l)))

noncomputable def discretize_entail_wit_3 : Prop :=
  (
forall (dest_map_pre : Int) (n_pre : Int) (src_pre : Int) (src_l : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) ,
  (intArray.full src_pre n_pre src_l)
  ** (intArray.full dest_map_pre i (sublist ((0 : Int)) (i) (src_l)))
  ** (intArray.undef_seg dest_map_pre i n_pre)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 50000) ”
  &&  (intArray.full src_pre n_pre src_l)
  ** (intArray.full dest_map_pre n_pre src_l)
) \/
(
forall (dest_map_pre : Int) (n_pre : Int) (src_l : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) ,
  (intArray.full dest_map_pre i (sublist ((0 : Int)) (i) (src_l)))
|--
  (intArray.full dest_map_pre n_pre src_l)
)

noncomputable def discretize_entail_wit_3_split_goal_spatial : Prop :=
  forall (dest_map_pre : Int) (n_pre : Int) (src_l : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) ,
  (intArray.full dest_map_pre i (sublist ((0 : Int)) (i) (src_l)))
|--
  (intArray.full dest_map_pre n_pre src_l)

noncomputable def discretize_entail_wit_4 : Prop :=
  (
forall (dest_map_pre : Int) (n_pre : Int) (src_pre : Int) (src_l : (List Int)) (l1 : (List Int)) (PreH1 : (permutation src_l l1)) (PreH2 : (increasing l1)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) ,
  (intArray.full dest_map_pre n_pre l1)
  ** (intArray.full src_pre n_pre src_l)
|--
  EX sorted_l : (List Int), EX cur_l : (List Int),
  “ (n_pre <= 50000) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) < 1) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= n_pre) ” &&
  “ (dedup_scan_inv src_l sorted_l cur_l (0 : Int) 1) ”
  &&  (intArray.full src_pre n_pre src_l)
  ** (intArray.full dest_map_pre n_pre cur_l)
) \/
(
forall (n_pre : Int) (src_l : (List Int)) (l1 : (List Int)) (PreH1 : (permutation src_l l1)) (PreH2 : (increasing l1)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) ,
  TT && emp 
|--
  EX sorted_l : (List Int),
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) < 1) ” &&
  “ (1 <= 1) ” &&
  “ (dedup_scan_inv src_l sorted_l l1 (0 : Int) 1) ”
  &&  emp
)

noncomputable def discretize_entail_wit_5_1 : Prop :=
  (
forall (dest_map_pre : Int) (n_pre : Int) (src_pre : Int) (src_l : (List Int)) (sorted_l_2 : (List Int)) (cur_l_2 : (List Int)) (fast : Int) (slow : Int) (PreH1 : ((Znth fast cur_l_2 (0 : Int)) ≠ (Znth slow cur_l_2 (0 : Int)))) (PreH2 : (fast < n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((0 : Int) <= slow)) (PreH5 : (slow < fast)) (PreH6 : (1 <= fast)) (PreH7 : (fast <= n_pre)) (PreH8 : (dedup_scan_inv src_l sorted_l_2 cur_l_2 slow fast)) ,
  (intArray.full dest_map_pre n_pre (replace_Znth ((slow + 1)) ((Znth fast cur_l_2 (0 : Int))) (cur_l_2)))
  ** (intArray.full src_pre n_pre src_l)
|--
  EX sorted_l : (List Int), EX cur_l : (List Int),
  “ (n_pre <= 50000) ” &&
  “ ((0 : Int) <= (slow + 1)) ” &&
  “ ((slow + 1) < (fast + 1)) ” &&
  “ (1 <= (fast + 1)) ” &&
  “ ((fast + 1) <= n_pre) ” &&
  “ (dedup_scan_inv src_l sorted_l cur_l (slow + 1) (fast + 1)) ”
  &&  (intArray.full src_pre n_pre src_l)
  ** (intArray.full dest_map_pre n_pre cur_l)
) \/
(
forall (n_pre : Int) (src_l : (List Int)) (sorted_l_2 : (List Int)) (cur_l_2 : (List Int)) (fast : Int) (slow : Int) (PreH1 : ((Znth fast cur_l_2 (0 : Int)) ≠ (Znth slow cur_l_2 (0 : Int)))) (PreH2 : (fast < n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((0 : Int) <= slow)) (PreH5 : (slow < fast)) (PreH6 : (1 <= fast)) (PreH7 : (fast <= n_pre)) (PreH8 : (dedup_scan_inv src_l sorted_l_2 cur_l_2 slow fast)) ,
  TT && emp 
|--
  EX sorted_l : (List Int),
  “ ((0 : Int) <= (slow + 1)) ” &&
  “ ((slow + 1) < (fast + 1)) ” &&
  “ (1 <= (fast + 1)) ” &&
  “ ((fast + 1) <= n_pre) ” &&
  “ (dedup_scan_inv src_l sorted_l (replace_Znth ((slow + 1)) ((Znth fast cur_l_2 (0 : Int))) (cur_l_2)) (slow + 1) (fast + 1)) ”
  &&  emp
)

noncomputable def discretize_entail_wit_5_2 : Prop :=
  (
forall (dest_map_pre : Int) (n_pre : Int) (src_pre : Int) (src_l : (List Int)) (sorted_l_2 : (List Int)) (cur_l_2 : (List Int)) (fast : Int) (slow : Int) (PreH1 : ((Znth fast cur_l_2 (0 : Int)) = (Znth slow cur_l_2 (0 : Int)))) (PreH2 : (fast < n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((0 : Int) <= slow)) (PreH5 : (slow < fast)) (PreH6 : (1 <= fast)) (PreH7 : (fast <= n_pre)) (PreH8 : (dedup_scan_inv src_l sorted_l_2 cur_l_2 slow fast)) ,
  (intArray.full dest_map_pre n_pre cur_l_2)
  ** (intArray.full src_pre n_pre src_l)
|--
  EX sorted_l : (List Int), EX cur_l : (List Int),
  “ (n_pre <= 50000) ” &&
  “ ((0 : Int) <= slow) ” &&
  “ (slow < (fast + 1)) ” &&
  “ (1 <= (fast + 1)) ” &&
  “ ((fast + 1) <= n_pre) ” &&
  “ (dedup_scan_inv src_l sorted_l cur_l slow (fast + 1)) ”
  &&  (intArray.full src_pre n_pre src_l)
  ** (intArray.full dest_map_pre n_pre cur_l)
) \/
(
forall (n_pre : Int) (src_l : (List Int)) (sorted_l_2 : (List Int)) (cur_l_2 : (List Int)) (fast : Int) (slow : Int) (PreH1 : ((Znth fast cur_l_2 (0 : Int)) = (Znth slow cur_l_2 (0 : Int)))) (PreH2 : (fast < n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((0 : Int) <= slow)) (PreH5 : (slow < fast)) (PreH6 : (1 <= fast)) (PreH7 : (fast <= n_pre)) (PreH8 : (dedup_scan_inv src_l sorted_l_2 cur_l_2 slow fast)) ,
  TT && emp 
|--
  EX sorted_l : (List Int),
  “ (slow < (fast + 1)) ” &&
  “ (1 <= (fast + 1)) ” &&
  “ ((fast + 1) <= n_pre) ” &&
  “ (dedup_scan_inv src_l sorted_l cur_l_2 slow (fast + 1)) ”
  &&  emp
)

noncomputable def discretize_return_wit_1 : Prop :=
  (
forall (dest_map_pre : Int) (n_pre : Int) (src_pre : Int) (src_l : (List Int)) (sorted_l : (List Int)) (cur_l : (List Int)) (fast : Int) (slow : Int) (PreH1 : (fast >= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((0 : Int) <= slow)) (PreH4 : (slow < fast)) (PreH5 : (1 <= fast)) (PreH6 : (fast <= n_pre)) (PreH7 : (dedup_scan_inv src_l sorted_l cur_l slow fast)) ,
  (intArray.full src_pre n_pre src_l)
  ** (intArray.full dest_map_pre n_pre cur_l)
|--
  EX out_l : (List Int),
  “ (discretize_result src_l out_l (slow + 1)) ”
  &&  (intArray.full src_pre n_pre src_l)
  ** (intArray.full dest_map_pre n_pre out_l)
) \/
(
forall (n_pre : Int) (src_l : (List Int)) (sorted_l : (List Int)) (cur_l : (List Int)) (fast : Int) (slow : Int) (PreH1 : (fast >= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((0 : Int) <= slow)) (PreH4 : (slow < fast)) (PreH5 : (1 <= fast)) (PreH6 : (fast <= n_pre)) (PreH7 : (dedup_scan_inv src_l sorted_l cur_l slow fast)) ,
  TT && emp 
|--
  “ (discretize_result src_l cur_l (slow + 1)) ”
  &&  emp
)

noncomputable def discretize_return_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (src_l : (List Int)) (sorted_l : (List Int)) (cur_l : (List Int)) (fast : Int) (slow : Int) (PreH1 : (fast >= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((0 : Int) <= slow)) (PreH4 : (slow < fast)) (PreH5 : (1 <= fast)) (PreH6 : (fast <= n_pre)) (PreH7 : (dedup_scan_inv src_l sorted_l cur_l slow fast)) ,
  (discretize_result src_l cur_l (slow + 1))

noncomputable def discretize_partial_solve_wit_1 : Prop :=
  forall (dest_map_pre : Int) (n_pre : Int) (src_pre : Int) (src_l : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) ,
  (intArray.full src_pre n_pre src_l)
  ** (intArray.full dest_map_pre i (sublist ((0 : Int)) (i) (src_l)))
  ** (intArray.undef_seg dest_map_pre i n_pre)
|--
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ”
  &&  (((src_pre + (i * sizeof(INT)))) # Int |-> ((Znth i src_l (0 : Int))))
  ** (intArray.missing_i src_pre i (0 : Int) n_pre src_l)
  ** (intArray.full dest_map_pre i (sublist ((0 : Int)) (i) (src_l)))
  ** (intArray.undef_seg dest_map_pre i n_pre)

noncomputable def discretize_partial_solve_wit_2 : Prop :=
  forall (dest_map_pre : Int) (n_pre : Int) (src_pre : Int) (src_l : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) ,
  (intArray.full src_pre n_pre src_l)
  ** (intArray.full dest_map_pre i (sublist ((0 : Int)) (i) (src_l)))
  ** (intArray.undef_seg dest_map_pre i n_pre)
|--
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ”
  &&  (((dest_map_pre + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg dest_map_pre (i + 1) n_pre)
  ** (intArray.full src_pre n_pre src_l)
  ** (intArray.full dest_map_pre i (sublist ((0 : Int)) (i) (src_l)))

noncomputable def discretize_partial_solve_wit_3_pure : Prop :=
  forall (dest_map_pre : Int) (n_pre : Int) (src_pre : Int) (src_l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 50000)) ,
  ((( &( "src" ) )) # Ptr |-> (src_pre))
  ** ((( &( "dest_map" ) )) # Ptr |-> (dest_map_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full src_pre n_pre src_l)
  ** (intArray.full dest_map_pre n_pre src_l)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 50000) ”

noncomputable def discretize_partial_solve_wit_3_aux : Prop :=
  forall (dest_map_pre : Int) (n_pre : Int) (src_pre : Int) (src_l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 50000)) ,
  (intArray.full src_pre n_pre src_l)
  ** (intArray.full dest_map_pre n_pre src_l)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 50000) ”
  &&  (intArray.full dest_map_pre n_pre src_l)
  ** (intArray.full src_pre n_pre src_l)

noncomputable def discretize_partial_solve_wit_3 : Prop := discretize_partial_solve_wit_3_pure -> discretize_partial_solve_wit_3_aux

noncomputable def discretize_partial_solve_wit_4 : Prop :=
  forall (dest_map_pre : Int) (n_pre : Int) (src_pre : Int) (src_l : (List Int)) (sorted_l : (List Int)) (cur_l : (List Int)) (fast : Int) (slow : Int) (PreH1 : (fast < n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((0 : Int) <= slow)) (PreH4 : (slow < fast)) (PreH5 : (1 <= fast)) (PreH6 : (fast <= n_pre)) (PreH7 : (dedup_scan_inv src_l sorted_l cur_l slow fast)) ,
  (intArray.full src_pre n_pre src_l)
  ** (intArray.full dest_map_pre n_pre cur_l)
|--
  “ (fast < n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((0 : Int) <= slow) ” &&
  “ (slow < fast) ” &&
  “ (1 <= fast) ” &&
  “ (fast <= n_pre) ” &&
  “ (dedup_scan_inv src_l sorted_l cur_l slow fast) ”
  &&  (((dest_map_pre + (fast * sizeof(INT)))) # Int |-> ((Znth fast cur_l (0 : Int))))
  ** (intArray.missing_i dest_map_pre fast (0 : Int) n_pre cur_l)
  ** (intArray.full src_pre n_pre src_l)

noncomputable def discretize_partial_solve_wit_5 : Prop :=
  forall (dest_map_pre : Int) (n_pre : Int) (src_pre : Int) (src_l : (List Int)) (sorted_l : (List Int)) (cur_l : (List Int)) (fast : Int) (slow : Int) (PreH1 : (fast < n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((0 : Int) <= slow)) (PreH4 : (slow < fast)) (PreH5 : (1 <= fast)) (PreH6 : (fast <= n_pre)) (PreH7 : (dedup_scan_inv src_l sorted_l cur_l slow fast)) ,
  (intArray.full dest_map_pre n_pre cur_l)
  ** (intArray.full src_pre n_pre src_l)
|--
  “ (fast < n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((0 : Int) <= slow) ” &&
  “ (slow < fast) ” &&
  “ (1 <= fast) ” &&
  “ (fast <= n_pre) ” &&
  “ (dedup_scan_inv src_l sorted_l cur_l slow fast) ”
  &&  (((dest_map_pre + (slow * sizeof(INT)))) # Int |-> ((Znth slow cur_l (0 : Int))))
  ** (intArray.missing_i dest_map_pre slow (0 : Int) n_pre cur_l)
  ** (intArray.full src_pre n_pre src_l)

noncomputable def discretize_partial_solve_wit_6 : Prop :=
  forall (dest_map_pre : Int) (n_pre : Int) (src_pre : Int) (src_l : (List Int)) (sorted_l : (List Int)) (cur_l : (List Int)) (fast : Int) (slow : Int) (PreH1 : ((Znth fast cur_l (0 : Int)) ≠ (Znth slow cur_l (0 : Int)))) (PreH2 : (fast < n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((0 : Int) <= slow)) (PreH5 : (slow < fast)) (PreH6 : (1 <= fast)) (PreH7 : (fast <= n_pre)) (PreH8 : (dedup_scan_inv src_l sorted_l cur_l slow fast)) ,
  (intArray.full dest_map_pre n_pre cur_l)
  ** (intArray.full src_pre n_pre src_l)
|--
  “ ((Znth fast cur_l (0 : Int)) ≠ (Znth slow cur_l (0 : Int))) ” &&
  “ (fast < n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((0 : Int) <= slow) ” &&
  “ (slow < fast) ” &&
  “ (1 <= fast) ” &&
  “ (fast <= n_pre) ” &&
  “ (dedup_scan_inv src_l sorted_l cur_l slow fast) ”
  &&  (((dest_map_pre + (fast * sizeof(INT)))) # Int |-> ((Znth fast cur_l (0 : Int))))
  ** (intArray.missing_i dest_map_pre fast (0 : Int) n_pre cur_l)
  ** (intArray.full src_pre n_pre src_l)

noncomputable def discretize_partial_solve_wit_7 : Prop :=
  forall (dest_map_pre : Int) (n_pre : Int) (src_pre : Int) (src_l : (List Int)) (sorted_l : (List Int)) (cur_l : (List Int)) (fast : Int) (slow : Int) (PreH1 : ((Znth fast cur_l (0 : Int)) ≠ (Znth slow cur_l (0 : Int)))) (PreH2 : (fast < n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((0 : Int) <= slow)) (PreH5 : (slow < fast)) (PreH6 : (1 <= fast)) (PreH7 : (fast <= n_pre)) (PreH8 : (dedup_scan_inv src_l sorted_l cur_l slow fast)) ,
  (intArray.full dest_map_pre n_pre cur_l)
  ** (intArray.full src_pre n_pre src_l)
|--
  “ ((Znth fast cur_l (0 : Int)) ≠ (Znth slow cur_l (0 : Int))) ” &&
  “ (fast < n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((0 : Int) <= slow) ” &&
  “ (slow < fast) ” &&
  “ (1 <= fast) ” &&
  “ (fast <= n_pre) ” &&
  “ (dedup_scan_inv src_l sorted_l cur_l slow fast) ”
  &&  (((dest_map_pre + ((slow + 1) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i dest_map_pre (slow + 1) (0 : Int) n_pre cur_l)
  ** (intArray.full src_pre n_pre src_l)

noncomputable def query_forward_safety_wit_1 : Prop :=
  forall (target_pre : Int) (map_size_pre : Int) (map_pre : Int) (map_l : (List Int)) (PreH1 : (map_size_pre <= 50000)) (PreH2 : (strict_increasing map_l)) ,
  ((( &( "low" ) )) # Int |->_)
  ** ((( &( "map" ) )) # Ptr |-> (map_pre))
  ** ((( &( "map_size" ) )) # Int |-> (map_size_pre))
  ** ((( &( "target" ) )) # Int |-> (target_pre))
  ** (intArray.full map_pre map_size_pre map_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def query_forward_safety_wit_2 : Prop :=
  (
forall (target_pre : Int) (map_size_pre : Int) (map_pre : Int) (map_l : (List Int)) (PreH1 : (map_size_pre <= 50000)) (PreH2 : (strict_increasing map_l)) ,
  ((( &( "high" ) )) # Int |->_)
  ** ((( &( "low" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "map" ) )) # Ptr |-> (map_pre))
  ** ((( &( "map_size" ) )) # Int |-> (map_size_pre))
  ** ((( &( "target" ) )) # Int |-> (target_pre))
  ** (intArray.full map_pre map_size_pre map_l)
|--
  “ ((map_size_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (map_size_pre - 1)) ”
) \/
(
forall (target_pre : Int) (map_size_pre : Int) (map_pre : Int) (map_l : (List Int)) (PreH1 : (map_size_pre <= 50000)) (PreH2 : (strict_increasing map_l)) ,
  ((( &( "high" ) )) # Int |->_)
  ** ((( &( "low" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "map" ) )) # Ptr |-> (map_pre))
  ** ((( &( "map_size" ) )) # Int |-> (map_size_pre))
  ** ((( &( "target" ) )) # Int |-> (target_pre))
  ** (intArray.full map_pre map_size_pre map_l)
|--
  “ ((map_size_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (map_size_pre - 1)) ”
)

noncomputable def query_forward_safety_wit_2_split_goal_1 : Prop :=
  forall (target_pre : Int) (map_size_pre : Int) (map_pre : Int) (map_l : (List Int)) (PreH1 : (map_size_pre <= 50000)) (PreH2 : (strict_increasing map_l)) ,
  ((( &( "high" ) )) # Int |->_)
  ** ((( &( "low" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "map" ) )) # Ptr |-> (map_pre))
  ** ((( &( "map_size" ) )) # Int |-> (map_size_pre))
  ** ((( &( "target" ) )) # Int |-> (target_pre))
  ** (intArray.full map_pre map_size_pre map_l)
|--
  “ ((map_size_pre - 1) <= INT_MAX) ”

noncomputable def query_forward_safety_wit_2_split_goal_2 : Prop :=
  forall (target_pre : Int) (map_size_pre : Int) (map_pre : Int) (map_l : (List Int)) (PreH1 : (map_size_pre <= 50000)) (PreH2 : (strict_increasing map_l)) ,
  ((( &( "high" ) )) # Int |->_)
  ** ((( &( "low" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "map" ) )) # Ptr |-> (map_pre))
  ** ((( &( "map_size" ) )) # Int |-> (map_size_pre))
  ** ((( &( "target" ) )) # Int |-> (target_pre))
  ** (intArray.full map_pre map_size_pre map_l)
|--
  “ ((INT_MIN) <= (map_size_pre - 1)) ”

noncomputable def query_forward_safety_wit_3 : Prop :=
  forall (target_pre : Int) (map_size_pre : Int) (map_pre : Int) (map_l : (List Int)) (PreH1 : (map_size_pre <= 50000)) (PreH2 : (strict_increasing map_l)) ,
  ((( &( "high" ) )) # Int |->_)
  ** ((( &( "low" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "map" ) )) # Ptr |-> (map_pre))
  ** ((( &( "map_size" ) )) # Int |-> (map_size_pre))
  ** ((( &( "target" ) )) # Int |-> (target_pre))
  ** (intArray.full map_pre map_size_pre map_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def query_forward_safety_wit_4 : Prop :=
  (
forall (target_pre : Int) (map_size_pre : Int) (map_pre : Int) (map_l : (List Int)) (high : Int) (low : Int) (PreH1 : (low <= high)) (PreH2 : (map_size_pre <= 50000)) (PreH3 : (strict_increasing map_l)) (PreH4 : ((0 : Int) <= low)) (PreH5 : (low <= (high + 1))) (PreH6 : (high < map_size_pre)) (PreH7 : (query_forward_search_inv map_l map_size_pre target_pre low high)) ,
  ((( &( "mid" ) )) # Int |->_)
  ** ((( &( "map" ) )) # Ptr |-> (map_pre))
  ** ((( &( "map_size" ) )) # Int |-> (map_size_pre))
  ** ((( &( "target" ) )) # Int |-> (target_pre))
  ** ((( &( "low" ) )) # Int |-> (low))
  ** ((( &( "high" ) )) # Int |-> (high))
  ** (intArray.full map_pre map_size_pre map_l)
|--
  “ ((low + (Z.quot (high - low) 2)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (low + (Z.quot (high - low) 2))) ”
) \/
(
forall (target_pre : Int) (map_size_pre : Int) (map_pre : Int) (map_l : (List Int)) (high : Int) (low : Int) (PreH1 : (low <= high)) (PreH2 : (map_size_pre <= 50000)) (PreH3 : (strict_increasing map_l)) (PreH4 : ((0 : Int) <= low)) (PreH5 : (low <= (high + 1))) (PreH6 : (high < map_size_pre)) (PreH7 : (query_forward_search_inv map_l map_size_pre target_pre low high)) ,
  ((( &( "mid" ) )) # Int |->_)
  ** ((( &( "map" ) )) # Ptr |-> (map_pre))
  ** ((( &( "map_size" ) )) # Int |-> (map_size_pre))
  ** ((( &( "target" ) )) # Int |-> (target_pre))
  ** ((( &( "low" ) )) # Int |-> (low))
  ** ((( &( "high" ) )) # Int |-> (high))
  ** (intArray.full map_pre map_size_pre map_l)
|--
  “ ((low + (Z.quot (high - low) 2)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (low + (Z.quot (high - low) 2))) ”
)

noncomputable def query_forward_safety_wit_4_split_goal_1 : Prop :=
  forall (target_pre : Int) (map_size_pre : Int) (map_pre : Int) (map_l : (List Int)) (high : Int) (low : Int) (PreH1 : (low <= high)) (PreH2 : (map_size_pre <= 50000)) (PreH3 : (strict_increasing map_l)) (PreH4 : ((0 : Int) <= low)) (PreH5 : (low <= (high + 1))) (PreH6 : (high < map_size_pre)) (PreH7 : (query_forward_search_inv map_l map_size_pre target_pre low high)) ,
  ((( &( "mid" ) )) # Int |->_)
  ** ((( &( "map" ) )) # Ptr |-> (map_pre))
  ** ((( &( "map_size" ) )) # Int |-> (map_size_pre))
  ** ((( &( "target" ) )) # Int |-> (target_pre))
  ** ((( &( "low" ) )) # Int |-> (low))
  ** ((( &( "high" ) )) # Int |-> (high))
  ** (intArray.full map_pre map_size_pre map_l)
|--
  “ ((low + (Z.quot (high - low) 2)) <= INT_MAX) ”

noncomputable def query_forward_safety_wit_4_split_goal_2 : Prop :=
  forall (target_pre : Int) (map_size_pre : Int) (map_pre : Int) (map_l : (List Int)) (high : Int) (low : Int) (PreH1 : (low <= high)) (PreH2 : (map_size_pre <= 50000)) (PreH3 : (strict_increasing map_l)) (PreH4 : ((0 : Int) <= low)) (PreH5 : (low <= (high + 1))) (PreH6 : (high < map_size_pre)) (PreH7 : (query_forward_search_inv map_l map_size_pre target_pre low high)) ,
  ((( &( "mid" ) )) # Int |->_)
  ** ((( &( "map" ) )) # Ptr |-> (map_pre))
  ** ((( &( "map_size" ) )) # Int |-> (map_size_pre))
  ** ((( &( "target" ) )) # Int |-> (target_pre))
  ** ((( &( "low" ) )) # Int |-> (low))
  ** ((( &( "high" ) )) # Int |-> (high))
  ** (intArray.full map_pre map_size_pre map_l)
|--
  “ ((INT_MIN) <= (low + (Z.quot (high - low) 2))) ”

noncomputable def query_forward_safety_wit_5 : Prop :=
  forall (target_pre : Int) (map_size_pre : Int) (map_pre : Int) (map_l : (List Int)) (high : Int) (low : Int) (PreH1 : (low <= high)) (PreH2 : (map_size_pre <= 50000)) (PreH3 : (strict_increasing map_l)) (PreH4 : ((0 : Int) <= low)) (PreH5 : (low <= (high + 1))) (PreH6 : (high < map_size_pre)) (PreH7 : (query_forward_search_inv map_l map_size_pre target_pre low high)) ,
  ((( &( "mid" ) )) # Int |->_)
  ** ((( &( "map" ) )) # Ptr |-> (map_pre))
  ** ((( &( "map_size" ) )) # Int |-> (map_size_pre))
  ** ((( &( "target" ) )) # Int |-> (target_pre))
  ** ((( &( "low" ) )) # Int |-> (low))
  ** ((( &( "high" ) )) # Int |-> (high))
  ** (intArray.full map_pre map_size_pre map_l)
|--
  “ (((high - low) ≠ (INT_MIN)) ∨ (2 ≠ (-1))) ” &&
  “ (2 ≠ (0 : Int)) ”

noncomputable def query_forward_safety_wit_6 : Prop :=
  forall (target_pre : Int) (map_size_pre : Int) (map_pre : Int) (map_l : (List Int)) (high : Int) (low : Int) (PreH1 : (low <= high)) (PreH2 : (map_size_pre <= 50000)) (PreH3 : (strict_increasing map_l)) (PreH4 : ((0 : Int) <= low)) (PreH5 : (low <= (high + 1))) (PreH6 : (high < map_size_pre)) (PreH7 : (query_forward_search_inv map_l map_size_pre target_pre low high)) ,
  ((( &( "mid" ) )) # Int |->_)
  ** ((( &( "map" ) )) # Ptr |-> (map_pre))
  ** ((( &( "map_size" ) )) # Int |-> (map_size_pre))
  ** ((( &( "target" ) )) # Int |-> (target_pre))
  ** ((( &( "low" ) )) # Int |-> (low))
  ** ((( &( "high" ) )) # Int |-> (high))
  ** (intArray.full map_pre map_size_pre map_l)
|--
  “ ((high - low) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (high - low)) ”

noncomputable def query_forward_safety_wit_7 : Prop :=
  forall (target_pre : Int) (map_size_pre : Int) (map_pre : Int) (map_l : (List Int)) (high : Int) (low : Int) (PreH1 : (low <= high)) (PreH2 : (map_size_pre <= 50000)) (PreH3 : (strict_increasing map_l)) (PreH4 : ((0 : Int) <= low)) (PreH5 : (low <= (high + 1))) (PreH6 : (high < map_size_pre)) (PreH7 : (query_forward_search_inv map_l map_size_pre target_pre low high)) ,
  ((( &( "mid" ) )) # Int |->_)
  ** ((( &( "map" ) )) # Ptr |-> (map_pre))
  ** ((( &( "map_size" ) )) # Int |-> (map_size_pre))
  ** ((( &( "target" ) )) # Int |-> (target_pre))
  ** ((( &( "low" ) )) # Int |-> (low))
  ** ((( &( "high" ) )) # Int |-> (high))
  ** (intArray.full map_pre map_size_pre map_l)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def query_forward_safety_wit_8 : Prop :=
  forall (target_pre : Int) (map_size_pre : Int) (map_pre : Int) (map_l : (List Int)) (low : Int) (mid : Int) (high : Int) (PreH1 : ((Znth mid map_l (0 : Int)) < target_pre)) (PreH2 : ((Znth mid map_l (0 : Int)) ≠ target_pre)) (PreH3 : (map_size_pre <= 50000)) (PreH4 : (strict_increasing map_l)) (PreH5 : ((0 : Int) <= low)) (PreH6 : (low <= mid)) (PreH7 : (mid <= high)) (PreH8 : (high < map_size_pre)) (PreH9 : (query_forward_search_inv map_l map_size_pre target_pre low high)) ,
  (intArray.full map_pre map_size_pre map_l)
  ** ((( &( "map" ) )) # Ptr |-> (map_pre))
  ** ((( &( "map_size" ) )) # Int |-> (map_size_pre))
  ** ((( &( "target" ) )) # Int |-> (target_pre))
  ** ((( &( "low" ) )) # Int |-> (low))
  ** ((( &( "mid" ) )) # Int |-> (mid))
  ** ((( &( "high" ) )) # Int |-> (high))
|--
  “ ((mid + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (mid + 1)) ”

noncomputable def query_forward_safety_wit_9 : Prop :=
  forall (target_pre : Int) (map_size_pre : Int) (map_pre : Int) (map_l : (List Int)) (low : Int) (mid : Int) (high : Int) (PreH1 : ((Znth mid map_l (0 : Int)) < target_pre)) (PreH2 : ((Znth mid map_l (0 : Int)) ≠ target_pre)) (PreH3 : (map_size_pre <= 50000)) (PreH4 : (strict_increasing map_l)) (PreH5 : ((0 : Int) <= low)) (PreH6 : (low <= mid)) (PreH7 : (mid <= high)) (PreH8 : (high < map_size_pre)) (PreH9 : (query_forward_search_inv map_l map_size_pre target_pre low high)) ,
  (intArray.full map_pre map_size_pre map_l)
  ** ((( &( "map" ) )) # Ptr |-> (map_pre))
  ** ((( &( "map_size" ) )) # Int |-> (map_size_pre))
  ** ((( &( "target" ) )) # Int |-> (target_pre))
  ** ((( &( "low" ) )) # Int |-> (low))
  ** ((( &( "mid" ) )) # Int |-> (mid))
  ** ((( &( "high" ) )) # Int |-> (high))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def query_forward_safety_wit_10 : Prop :=
  forall (target_pre : Int) (map_size_pre : Int) (map_pre : Int) (map_l : (List Int)) (low : Int) (mid : Int) (high : Int) (PreH1 : ((Znth mid map_l (0 : Int)) >= target_pre)) (PreH2 : ((Znth mid map_l (0 : Int)) ≠ target_pre)) (PreH3 : (map_size_pre <= 50000)) (PreH4 : (strict_increasing map_l)) (PreH5 : ((0 : Int) <= low)) (PreH6 : (low <= mid)) (PreH7 : (mid <= high)) (PreH8 : (high < map_size_pre)) (PreH9 : (query_forward_search_inv map_l map_size_pre target_pre low high)) ,
  (intArray.full map_pre map_size_pre map_l)
  ** ((( &( "map" ) )) # Ptr |-> (map_pre))
  ** ((( &( "map_size" ) )) # Int |-> (map_size_pre))
  ** ((( &( "target" ) )) # Int |-> (target_pre))
  ** ((( &( "low" ) )) # Int |-> (low))
  ** ((( &( "mid" ) )) # Int |-> (mid))
  ** ((( &( "high" ) )) # Int |-> (high))
|--
  “ ((mid - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (mid - 1)) ”

noncomputable def query_forward_safety_wit_11 : Prop :=
  forall (target_pre : Int) (map_size_pre : Int) (map_pre : Int) (map_l : (List Int)) (low : Int) (mid : Int) (high : Int) (PreH1 : ((Znth mid map_l (0 : Int)) >= target_pre)) (PreH2 : ((Znth mid map_l (0 : Int)) ≠ target_pre)) (PreH3 : (map_size_pre <= 50000)) (PreH4 : (strict_increasing map_l)) (PreH5 : ((0 : Int) <= low)) (PreH6 : (low <= mid)) (PreH7 : (mid <= high)) (PreH8 : (high < map_size_pre)) (PreH9 : (query_forward_search_inv map_l map_size_pre target_pre low high)) ,
  (intArray.full map_pre map_size_pre map_l)
  ** ((( &( "map" ) )) # Ptr |-> (map_pre))
  ** ((( &( "map_size" ) )) # Int |-> (map_size_pre))
  ** ((( &( "target" ) )) # Int |-> (target_pre))
  ** ((( &( "low" ) )) # Int |-> (low))
  ** ((( &( "mid" ) )) # Int |-> (mid))
  ** ((( &( "high" ) )) # Int |-> (high))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def query_forward_safety_wit_12 : Prop :=
  forall (target_pre : Int) (map_size_pre : Int) (map_pre : Int) (map_l : (List Int)) (high : Int) (low : Int) (PreH1 : (low > high)) (PreH2 : (map_size_pre <= 50000)) (PreH3 : (strict_increasing map_l)) (PreH4 : ((0 : Int) <= low)) (PreH5 : (low <= (high + 1))) (PreH6 : (high < map_size_pre)) (PreH7 : (query_forward_search_inv map_l map_size_pre target_pre low high)) ,
  ((( &( "map" ) )) # Ptr |-> (map_pre))
  ** ((( &( "map_size" ) )) # Int |-> (map_size_pre))
  ** ((( &( "target" ) )) # Int |-> (target_pre))
  ** ((( &( "low" ) )) # Int |-> (low))
  ** ((( &( "high" ) )) # Int |-> (high))
  ** (intArray.full map_pre map_size_pre map_l)
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def query_forward_safety_wit_13 : Prop :=
  forall (target_pre : Int) (map_size_pre : Int) (map_pre : Int) (map_l : (List Int)) (high : Int) (low : Int) (PreH1 : (low > high)) (PreH2 : (map_size_pre <= 50000)) (PreH3 : (strict_increasing map_l)) (PreH4 : ((0 : Int) <= low)) (PreH5 : (low <= (high + 1))) (PreH6 : (high < map_size_pre)) (PreH7 : (query_forward_search_inv map_l map_size_pre target_pre low high)) ,
  ((( &( "map" ) )) # Ptr |-> (map_pre))
  ** ((( &( "map_size" ) )) # Int |-> (map_size_pre))
  ** ((( &( "target" ) )) # Int |-> (target_pre))
  ** ((( &( "low" ) )) # Int |-> (low))
  ** ((( &( "high" ) )) # Int |-> (high))
  ** (intArray.full map_pre map_size_pre map_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def query_forward_entail_wit_1 : Prop :=
  (
forall (target_pre : Int) (map_size_pre : Int) (map_pre : Int) (map_l : (List Int)) (PreH1 : (map_size_pre <= 50000)) (PreH2 : (strict_increasing map_l)) ,
  (intArray.full map_pre map_size_pre map_l)
|--
  “ (map_size_pre <= 50000) ” &&
  “ (strict_increasing map_l) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= ((map_size_pre - 1) + 1)) ” &&
  “ ((map_size_pre - 1) < map_size_pre) ” &&
  “ (query_forward_search_inv map_l map_size_pre target_pre (0 : Int) (map_size_pre - 1)) ”
  &&  (intArray.full map_pre map_size_pre map_l)
) \/
(
forall (target_pre : Int) (map_size_pre : Int) (map_l : (List Int)) (PreH1 : (map_size_pre <= 50000)) (PreH2 : (strict_increasing map_l)) ,
  TT && emp 
|--
  “ (query_forward_search_inv map_l map_size_pre target_pre (0 : Int) (map_size_pre - 1)) ” &&
  “ ((0 : Int) <= ((map_size_pre - 1) + 1)) ”
  &&  emp
)

noncomputable def query_forward_entail_wit_1_split_goal_1 : Prop :=
  forall (target_pre : Int) (map_size_pre : Int) (map_l : (List Int)) (PreH1 : (map_size_pre <= 50000)) (PreH2 : (strict_increasing map_l)) ,
  (query_forward_search_inv map_l map_size_pre target_pre (0 : Int) (map_size_pre - 1))

noncomputable def query_forward_entail_wit_1_split_goal_2 : Prop :=
  forall (map_size_pre : Int) (map_l : (List Int)) (PreH1 : (map_size_pre <= 50000)) (PreH2 : (strict_increasing map_l)) ,
  ((0 : Int) <= ((map_size_pre - 1) + 1))

noncomputable def query_forward_entail_wit_2 : Prop :=
  (
forall (target_pre : Int) (map_size_pre : Int) (map_pre : Int) (map_l : (List Int)) (high : Int) (low : Int) (PreH1 : (low <= high)) (PreH2 : (map_size_pre <= 50000)) (PreH3 : (strict_increasing map_l)) (PreH4 : ((0 : Int) <= low)) (PreH5 : (low <= (high + 1))) (PreH6 : (high < map_size_pre)) (PreH7 : (query_forward_search_inv map_l map_size_pre target_pre low high)) ,
  (intArray.full map_pre map_size_pre map_l)
|--
  “ (map_size_pre <= 50000) ” &&
  “ (strict_increasing map_l) ” &&
  “ ((0 : Int) <= low) ” &&
  “ (low <= (low + (Z.quot (high - low) 2))) ” &&
  “ ((low + (Z.quot (high - low) 2)) <= high) ” &&
  “ (high < map_size_pre) ” &&
  “ (query_forward_search_inv map_l map_size_pre target_pre low high) ”
  &&  (intArray.full map_pre map_size_pre map_l)
) \/
(
forall (target_pre : Int) (map_size_pre : Int) (map_l : (List Int)) (high : Int) (low : Int) (PreH1 : (low <= high)) (PreH2 : (map_size_pre <= 50000)) (PreH3 : (strict_increasing map_l)) (PreH4 : ((0 : Int) <= low)) (PreH5 : (low <= (high + 1))) (PreH6 : (high < map_size_pre)) (PreH7 : (query_forward_search_inv map_l map_size_pre target_pre low high)) ,
  TT && emp 
|--
  “ ((low + (Z.quot (high - low) 2)) <= high) ” &&
  “ (low <= (low + (Z.quot (high - low) 2))) ”
  &&  emp
)

noncomputable def query_forward_entail_wit_2_split_goal_1 : Prop :=
  forall (target_pre : Int) (map_size_pre : Int) (map_l : (List Int)) (high : Int) (low : Int) (PreH1 : (low <= high)) (PreH2 : (map_size_pre <= 50000)) (PreH3 : (strict_increasing map_l)) (PreH4 : ((0 : Int) <= low)) (PreH5 : (low <= (high + 1))) (PreH6 : (high < map_size_pre)) (PreH7 : (query_forward_search_inv map_l map_size_pre target_pre low high)) ,
  ((low + (Z.quot (high - low) 2)) <= high)

noncomputable def query_forward_entail_wit_2_split_goal_2 : Prop :=
  forall (target_pre : Int) (map_size_pre : Int) (map_l : (List Int)) (high : Int) (low : Int) (PreH1 : (low <= high)) (PreH2 : (map_size_pre <= 50000)) (PreH3 : (strict_increasing map_l)) (PreH4 : ((0 : Int) <= low)) (PreH5 : (low <= (high + 1))) (PreH6 : (high < map_size_pre)) (PreH7 : (query_forward_search_inv map_l map_size_pre target_pre low high)) ,
  (low <= (low + (Z.quot (high - low) 2)))

noncomputable def query_forward_entail_wit_3_1 : Prop :=
  (
forall (target_pre : Int) (map_size_pre : Int) (map_pre : Int) (map_l : (List Int)) (low : Int) (mid : Int) (high : Int) (PreH1 : ((Znth mid map_l (0 : Int)) < target_pre)) (PreH2 : ((Znth mid map_l (0 : Int)) ≠ target_pre)) (PreH3 : (map_size_pre <= 50000)) (PreH4 : (strict_increasing map_l)) (PreH5 : ((0 : Int) <= low)) (PreH6 : (low <= mid)) (PreH7 : (mid <= high)) (PreH8 : (high < map_size_pre)) (PreH9 : (query_forward_search_inv map_l map_size_pre target_pre low high)) ,
  (intArray.full map_pre map_size_pre map_l)
|--
  “ (map_size_pre <= 50000) ” &&
  “ (strict_increasing map_l) ” &&
  “ ((0 : Int) <= (mid + 1)) ” &&
  “ ((mid + 1) <= (high + 1)) ” &&
  “ (high < map_size_pre) ” &&
  “ (query_forward_search_inv map_l map_size_pre target_pre (mid + 1) high) ”
  &&  (intArray.full map_pre map_size_pre map_l)
) \/
(
forall (target_pre : Int) (map_size_pre : Int) (map_l : (List Int)) (low : Int) (mid : Int) (high : Int) (PreH1 : ((Znth mid map_l (0 : Int)) < target_pre)) (PreH2 : ((Znth mid map_l (0 : Int)) ≠ target_pre)) (PreH3 : (map_size_pre <= 50000)) (PreH4 : (strict_increasing map_l)) (PreH5 : ((0 : Int) <= low)) (PreH6 : (low <= mid)) (PreH7 : (mid <= high)) (PreH8 : (high < map_size_pre)) (PreH9 : (query_forward_search_inv map_l map_size_pre target_pre low high)) ,
  TT && emp 
|--
  “ (query_forward_search_inv map_l map_size_pre target_pre (mid + 1) high) ”
  &&  emp
)

noncomputable def query_forward_entail_wit_3_1_split_goal_1 : Prop :=
  forall (target_pre : Int) (map_size_pre : Int) (map_l : (List Int)) (low : Int) (mid : Int) (high : Int) (PreH1 : ((Znth mid map_l (0 : Int)) < target_pre)) (PreH2 : ((Znth mid map_l (0 : Int)) ≠ target_pre)) (PreH3 : (map_size_pre <= 50000)) (PreH4 : (strict_increasing map_l)) (PreH5 : ((0 : Int) <= low)) (PreH6 : (low <= mid)) (PreH7 : (mid <= high)) (PreH8 : (high < map_size_pre)) (PreH9 : (query_forward_search_inv map_l map_size_pre target_pre low high)) ,
  (query_forward_search_inv map_l map_size_pre target_pre (mid + 1) high)

noncomputable def query_forward_entail_wit_3_2 : Prop :=
  (
forall (target_pre : Int) (map_size_pre : Int) (map_pre : Int) (map_l : (List Int)) (low : Int) (mid : Int) (high : Int) (PreH1 : ((Znth mid map_l (0 : Int)) >= target_pre)) (PreH2 : ((Znth mid map_l (0 : Int)) ≠ target_pre)) (PreH3 : (map_size_pre <= 50000)) (PreH4 : (strict_increasing map_l)) (PreH5 : ((0 : Int) <= low)) (PreH6 : (low <= mid)) (PreH7 : (mid <= high)) (PreH8 : (high < map_size_pre)) (PreH9 : (query_forward_search_inv map_l map_size_pre target_pre low high)) ,
  (intArray.full map_pre map_size_pre map_l)
|--
  “ (map_size_pre <= 50000) ” &&
  “ (strict_increasing map_l) ” &&
  “ ((0 : Int) <= low) ” &&
  “ (low <= ((mid - 1) + 1)) ” &&
  “ ((mid - 1) < map_size_pre) ” &&
  “ (query_forward_search_inv map_l map_size_pre target_pre low (mid - 1)) ”
  &&  (intArray.full map_pre map_size_pre map_l)
) \/
(
forall (target_pre : Int) (map_size_pre : Int) (map_l : (List Int)) (low : Int) (mid : Int) (high : Int) (PreH1 : ((Znth mid map_l (0 : Int)) >= target_pre)) (PreH2 : ((Znth mid map_l (0 : Int)) ≠ target_pre)) (PreH3 : (map_size_pre <= 50000)) (PreH4 : (strict_increasing map_l)) (PreH5 : ((0 : Int) <= low)) (PreH6 : (low <= mid)) (PreH7 : (mid <= high)) (PreH8 : (high < map_size_pre)) (PreH9 : (query_forward_search_inv map_l map_size_pre target_pre low high)) ,
  TT && emp 
|--
  “ (query_forward_search_inv map_l map_size_pre target_pre low (mid - 1)) ”
  &&  emp
)

noncomputable def query_forward_entail_wit_3_2_split_goal_1 : Prop :=
  forall (target_pre : Int) (map_size_pre : Int) (map_l : (List Int)) (low : Int) (mid : Int) (high : Int) (PreH1 : ((Znth mid map_l (0 : Int)) >= target_pre)) (PreH2 : ((Znth mid map_l (0 : Int)) ≠ target_pre)) (PreH3 : (map_size_pre <= 50000)) (PreH4 : (strict_increasing map_l)) (PreH5 : ((0 : Int) <= low)) (PreH6 : (low <= mid)) (PreH7 : (mid <= high)) (PreH8 : (high < map_size_pre)) (PreH9 : (query_forward_search_inv map_l map_size_pre target_pre low high)) ,
  (query_forward_search_inv map_l map_size_pre target_pre low (mid - 1))

noncomputable def query_forward_return_wit_1 : Prop :=
  (
forall (target_pre : Int) (map_size_pre : Int) (map_pre : Int) (map_l : (List Int)) (high : Int) (low : Int) (PreH1 : (low > high)) (PreH2 : (map_size_pre <= 50000)) (PreH3 : (strict_increasing map_l)) (PreH4 : ((0 : Int) <= low)) (PreH5 : (low <= (high + 1))) (PreH6 : (high < map_size_pre)) (PreH7 : (query_forward_search_inv map_l map_size_pre target_pre low high)) ,
  (intArray.full map_pre map_size_pre map_l)
|--
  “ (query_forward_result map_l target_pre (-1)) ”
  &&  (intArray.full map_pre map_size_pre map_l)
) \/
(
forall (target_pre : Int) (map_size_pre : Int) (map_l : (List Int)) (high : Int) (low : Int) (PreH1 : (low > high)) (PreH2 : (map_size_pre <= 50000)) (PreH3 : (strict_increasing map_l)) (PreH4 : ((0 : Int) <= low)) (PreH5 : (low <= (high + 1))) (PreH6 : (high < map_size_pre)) (PreH7 : (query_forward_search_inv map_l map_size_pre target_pre low high)) ,
  TT && emp 
|--
  “ (query_forward_result map_l target_pre (-1)) ”
  &&  emp
)

noncomputable def query_forward_return_wit_1_split_goal_1 : Prop :=
  forall (target_pre : Int) (map_size_pre : Int) (map_l : (List Int)) (high : Int) (low : Int) (PreH1 : (low > high)) (PreH2 : (map_size_pre <= 50000)) (PreH3 : (strict_increasing map_l)) (PreH4 : ((0 : Int) <= low)) (PreH5 : (low <= (high + 1))) (PreH6 : (high < map_size_pre)) (PreH7 : (query_forward_search_inv map_l map_size_pre target_pre low high)) ,
  (query_forward_result map_l target_pre (-1))

noncomputable def query_forward_return_wit_2 : Prop :=
  (
forall (target_pre : Int) (map_size_pre : Int) (map_pre : Int) (map_l : (List Int)) (low : Int) (mid : Int) (high : Int) (PreH1 : ((Znth mid map_l (0 : Int)) = target_pre)) (PreH2 : (map_size_pre <= 50000)) (PreH3 : (strict_increasing map_l)) (PreH4 : ((0 : Int) <= low)) (PreH5 : (low <= mid)) (PreH6 : (mid <= high)) (PreH7 : (high < map_size_pre)) (PreH8 : (query_forward_search_inv map_l map_size_pre target_pre low high)) ,
  (intArray.full map_pre map_size_pre map_l)
|--
  “ (query_forward_result map_l target_pre mid) ”
  &&  (intArray.full map_pre map_size_pre map_l)
) \/
(
forall (target_pre : Int) (map_size_pre : Int) (map_l : (List Int)) (low : Int) (mid : Int) (high : Int) (PreH1 : ((Znth mid map_l (0 : Int)) = target_pre)) (PreH2 : (map_size_pre <= 50000)) (PreH3 : (strict_increasing map_l)) (PreH4 : ((0 : Int) <= low)) (PreH5 : (low <= mid)) (PreH6 : (mid <= high)) (PreH7 : (high < map_size_pre)) (PreH8 : (query_forward_search_inv map_l map_size_pre target_pre low high)) ,
  TT && emp 
|--
  “ (query_forward_result map_l target_pre mid) ”
  &&  emp
)

noncomputable def query_forward_return_wit_2_split_goal_1 : Prop :=
  forall (target_pre : Int) (map_size_pre : Int) (map_l : (List Int)) (low : Int) (mid : Int) (high : Int) (PreH1 : ((Znth mid map_l (0 : Int)) = target_pre)) (PreH2 : (map_size_pre <= 50000)) (PreH3 : (strict_increasing map_l)) (PreH4 : ((0 : Int) <= low)) (PreH5 : (low <= mid)) (PreH6 : (mid <= high)) (PreH7 : (high < map_size_pre)) (PreH8 : (query_forward_search_inv map_l map_size_pre target_pre low high)) ,
  (query_forward_result map_l target_pre mid)

noncomputable def query_forward_partial_solve_wit_1 : Prop :=
  forall (target_pre : Int) (map_size_pre : Int) (map_pre : Int) (map_l : (List Int)) (low : Int) (mid : Int) (high : Int) (PreH1 : (map_size_pre <= 50000)) (PreH2 : (strict_increasing map_l)) (PreH3 : ((0 : Int) <= low)) (PreH4 : (low <= mid)) (PreH5 : (mid <= high)) (PreH6 : (high < map_size_pre)) (PreH7 : (query_forward_search_inv map_l map_size_pre target_pre low high)) ,
  (intArray.full map_pre map_size_pre map_l)
|--
  “ (map_size_pre <= 50000) ” &&
  “ (strict_increasing map_l) ” &&
  “ ((0 : Int) <= low) ” &&
  “ (low <= mid) ” &&
  “ (mid <= high) ” &&
  “ (high < map_size_pre) ” &&
  “ (query_forward_search_inv map_l map_size_pre target_pre low high) ”
  &&  (((map_pre + (mid * sizeof(INT)))) # Int |-> ((Znth mid map_l (0 : Int))))
  ** (intArray.missing_i map_pre mid (0 : Int) map_size_pre map_l)

noncomputable def query_forward_partial_solve_wit_2 : Prop :=
  forall (target_pre : Int) (map_size_pre : Int) (map_pre : Int) (map_l : (List Int)) (low : Int) (mid : Int) (high : Int) (PreH1 : ((Znth mid map_l (0 : Int)) ≠ target_pre)) (PreH2 : (map_size_pre <= 50000)) (PreH3 : (strict_increasing map_l)) (PreH4 : ((0 : Int) <= low)) (PreH5 : (low <= mid)) (PreH6 : (mid <= high)) (PreH7 : (high < map_size_pre)) (PreH8 : (query_forward_search_inv map_l map_size_pre target_pre low high)) ,
  (intArray.full map_pre map_size_pre map_l)
|--
  “ ((Znth mid map_l (0 : Int)) ≠ target_pre) ” &&
  “ (map_size_pre <= 50000) ” &&
  “ (strict_increasing map_l) ” &&
  “ ((0 : Int) <= low) ” &&
  “ (low <= mid) ” &&
  “ (mid <= high) ” &&
  “ (high < map_size_pre) ” &&
  “ (query_forward_search_inv map_l map_size_pre target_pre low high) ”
  &&  (((map_pre + (mid * sizeof(INT)))) # Int |-> ((Znth mid map_l (0 : Int))))
  ** (intArray.missing_i map_pre mid (0 : Int) map_size_pre map_l)


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
  proof_of_int_array_quicksort_safety_wit_1 : int_array_quicksort_safety_wit_1
  proof_of_int_array_quicksort_safety_wit_2 : int_array_quicksort_safety_wit_2
  proof_of_int_array_quicksort_safety_wit_3 : int_array_quicksort_safety_wit_3
  proof_of_int_array_quicksort_partial_solve_wit_1_pure : int_array_quicksort_partial_solve_wit_1_pure
  proof_of_int_array_quicksort_partial_solve_wit_1 : int_array_quicksort_partial_solve_wit_1
  proof_of_discretize_safety_wit_1 : discretize_safety_wit_1
  proof_of_discretize_safety_wit_2 : discretize_safety_wit_2
  proof_of_discretize_safety_wit_3 : discretize_safety_wit_3
  proof_of_discretize_safety_wit_4 : discretize_safety_wit_4
  proof_of_discretize_safety_wit_5 : discretize_safety_wit_5
  proof_of_discretize_safety_wit_6 : discretize_safety_wit_6
  proof_of_discretize_safety_wit_7 : discretize_safety_wit_7
  proof_of_discretize_safety_wit_8 : discretize_safety_wit_8
  proof_of_discretize_safety_wit_9 : discretize_safety_wit_9
  proof_of_discretize_partial_solve_wit_1 : discretize_partial_solve_wit_1
  proof_of_discretize_partial_solve_wit_2 : discretize_partial_solve_wit_2
  proof_of_discretize_partial_solve_wit_3_pure : discretize_partial_solve_wit_3_pure
  proof_of_discretize_partial_solve_wit_3 : discretize_partial_solve_wit_3
  proof_of_discretize_partial_solve_wit_4 : discretize_partial_solve_wit_4
  proof_of_discretize_partial_solve_wit_5 : discretize_partial_solve_wit_5
  proof_of_discretize_partial_solve_wit_6 : discretize_partial_solve_wit_6
  proof_of_discretize_partial_solve_wit_7 : discretize_partial_solve_wit_7
  proof_of_query_forward_safety_wit_1 : query_forward_safety_wit_1
  proof_of_query_forward_safety_wit_3 : query_forward_safety_wit_3
  proof_of_query_forward_safety_wit_5 : query_forward_safety_wit_5
  proof_of_query_forward_safety_wit_6 : query_forward_safety_wit_6
  proof_of_query_forward_safety_wit_7 : query_forward_safety_wit_7
  proof_of_query_forward_safety_wit_8 : query_forward_safety_wit_8
  proof_of_query_forward_safety_wit_9 : query_forward_safety_wit_9
  proof_of_query_forward_safety_wit_10 : query_forward_safety_wit_10
  proof_of_query_forward_safety_wit_11 : query_forward_safety_wit_11
  proof_of_query_forward_safety_wit_12 : query_forward_safety_wit_12
  proof_of_query_forward_safety_wit_13 : query_forward_safety_wit_13
  proof_of_query_forward_partial_solve_wit_1 : query_forward_partial_solve_wit_1
  proof_of_query_forward_partial_solve_wit_2 : query_forward_partial_solve_wit_2
  proof_of_partition_entail_wit_1 : partition_entail_wit_1
  proof_of_partition_entail_wit_2_1 : partition_entail_wit_2_1
  proof_of_partition_entail_wit_2_2 : partition_entail_wit_2_2
  proof_of_partition_return_wit_1 : partition_return_wit_1
  proof_of_quicksort_range_return_wit_1 : quicksort_range_return_wit_1
  proof_of_quicksort_range_return_wit_2 : quicksort_range_return_wit_2
  proof_of_quicksort_range_return_wit_3 : quicksort_range_return_wit_3
  proof_of_quicksort_range_return_wit_4 : quicksort_range_return_wit_4
  proof_of_int_array_quicksort_return_wit_1 : int_array_quicksort_return_wit_1
  proof_of_discretize_entail_wit_1 : discretize_entail_wit_1
  proof_of_discretize_entail_wit_2 : discretize_entail_wit_2
  proof_of_discretize_entail_wit_3 : discretize_entail_wit_3
  proof_of_discretize_entail_wit_4 : discretize_entail_wit_4
  proof_of_discretize_entail_wit_5_1 : discretize_entail_wit_5_1
  proof_of_discretize_entail_wit_5_2 : discretize_entail_wit_5_2
  proof_of_discretize_return_wit_1 : discretize_return_wit_1
  proof_of_query_forward_safety_wit_2 : query_forward_safety_wit_2
  proof_of_query_forward_safety_wit_4 : query_forward_safety_wit_4
  proof_of_query_forward_entail_wit_1 : query_forward_entail_wit_1
  proof_of_query_forward_entail_wit_2 : query_forward_entail_wit_2
  proof_of_query_forward_entail_wit_3_1 : query_forward_entail_wit_3_1
  proof_of_query_forward_entail_wit_3_2 : query_forward_entail_wit_3_2
  proof_of_query_forward_return_wit_1 : query_forward_return_wit_1
  proof_of_query_forward_return_wit_2 : query_forward_return_wit_2

end SimpleC.EE.LLM_bench.Algorithms.discretize.discretize_goal
