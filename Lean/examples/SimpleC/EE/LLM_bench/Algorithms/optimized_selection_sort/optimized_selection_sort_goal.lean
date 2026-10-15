import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.optimized_selection_sort.optimized_selection_sort_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.optimized_selection_sort.optimized_selection_sort_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance optimized_selection_sort_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def optimized_selection_sort_safety_wit_1 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : ((Zlength (input)) = n_pre)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre input)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def optimized_selection_sort_safety_wit_2 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (cur : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (cur)) = n_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (i < INT_MAX)) (PreH8 : (Permutation input cur)) (PreH9 : (increasing (sublist ((0 : Int)) (i) (cur)))) (PreH10 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur) ((0 : Int))) <= (Znth (q) (cur) ((0 : Int)))))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full a_pre n_pre cur)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def optimized_selection_sort_safety_wit_3 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (cur : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (cur)) = n_pre)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (i < INT_MAX)) (PreH8 : (Permutation input cur)) (PreH9 : (increasing (sublist ((0 : Int)) (i) (cur)))) (PreH10 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur) ((0 : Int))) <= (Znth (q) (cur) ((0 : Int)))))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full a_pre n_pre cur)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def optimized_selection_sort_safety_wit_4 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (cur : (List Int)) (PreH1 : ((i + 1) < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (cur)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (i < INT_MAX)) (PreH9 : (Permutation input cur)) (PreH10 : (increasing (sublist ((0 : Int)) (i) (cur)))) (PreH11 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur) ((0 : Int))) <= (Znth (q) (cur) ((0 : Int)))))) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "min_index" ) )) # Int |-> (i))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full a_pre n_pre cur)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def optimized_selection_sort_safety_wit_5 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (cur : (List Int)) (PreH1 : ((i + 1) < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (cur)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (i < INT_MAX)) (PreH9 : (Permutation input cur)) (PreH10 : (increasing (sublist ((0 : Int)) (i) (cur)))) (PreH11 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur) ((0 : Int))) <= (Znth (q) (cur) ((0 : Int)))))) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "min_index" ) )) # Int |-> (i))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full a_pre n_pre cur)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def optimized_selection_sort_safety_wit_6 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (j : Int) (min_index : Int) (i : Int) (cur : (List Int)) (PreH1 : ((Znth j cur (0 : Int)) < (Znth min_index cur (0 : Int)))) (PreH2 : (j < n_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : ((Zlength (cur)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : ((i + 1) < n_pre)) (PreH9 : (i <= min_index)) (PreH10 : (min_index < j)) (PreH11 : ((i + 1) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : (Permutation input cur)) (PreH14 : (increasing (sublist ((0 : Int)) (i) (cur)))) (PreH15 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur) ((0 : Int))) <= (Znth (q) (cur) ((0 : Int)))))) (PreH16 : (selection_minimum (sublist (i) (j) (cur)) (Znth (min_index) (cur) ((0 : Int))))) ,
  (intArray.full a_pre n_pre cur)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "min_index" ) )) # Int |-> (j))
  ** ((( &( "j" ) )) # Int |-> (j))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def optimized_selection_sort_safety_wit_7 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (j : Int) (min_index : Int) (i : Int) (cur : (List Int)) (PreH1 : ((Znth j cur (0 : Int)) >= (Znth min_index cur (0 : Int)))) (PreH2 : (j < n_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : ((Zlength (cur)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : ((i + 1) < n_pre)) (PreH9 : (i <= min_index)) (PreH10 : (min_index < j)) (PreH11 : ((i + 1) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : (Permutation input cur)) (PreH14 : (increasing (sublist ((0 : Int)) (i) (cur)))) (PreH15 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur) ((0 : Int))) <= (Znth (q) (cur) ((0 : Int)))))) (PreH16 : (selection_minimum (sublist (i) (j) (cur)) (Znth (min_index) (cur) ((0 : Int))))) ,
  (intArray.full a_pre n_pre cur)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "min_index" ) )) # Int |-> (min_index))
  ** ((( &( "j" ) )) # Int |-> (j))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def optimized_selection_sort_safety_wit_8 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (j : Int) (min_index : Int) (i : Int) (cur : (List Int)) (PreH1 : (min_index ≠ i)) (PreH2 : (j >= n_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : ((Zlength (cur)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : ((i + 1) < n_pre)) (PreH9 : (i <= min_index)) (PreH10 : (min_index < j)) (PreH11 : ((i + 1) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : (Permutation input cur)) (PreH14 : (increasing (sublist ((0 : Int)) (i) (cur)))) (PreH15 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur) ((0 : Int))) <= (Znth (q) (cur) ((0 : Int)))))) (PreH16 : (selection_minimum (sublist (i) (j) (cur)) (Znth (min_index) (cur) ((0 : Int))))) ,
  (intArray.full a_pre n_pre (replace_Znth (min_index) ((Znth i cur (0 : Int))) ((replace_Znth (i) ((Znth min_index cur (0 : Int))) (cur)))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def optimized_selection_sort_safety_wit_9 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (j : Int) (min_index : Int) (i : Int) (cur : (List Int)) (PreH1 : (min_index = i)) (PreH2 : (j >= n_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : ((Zlength (cur)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : ((i + 1) < n_pre)) (PreH9 : (i <= min_index)) (PreH10 : (min_index < j)) (PreH11 : ((i + 1) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : (Permutation input cur)) (PreH14 : (increasing (sublist ((0 : Int)) (i) (cur)))) (PreH15 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur) ((0 : Int))) <= (Znth (q) (cur) ((0 : Int)))))) (PreH16 : (selection_minimum (sublist (i) (j) (cur)) (Znth (min_index) (cur) ((0 : Int))))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full a_pre n_pre cur)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def optimized_selection_sort_entail_wit_1 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : ((Zlength (input)) = n_pre)) ,
  ((( &( "i" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre input)
|--
  EX i : Int, EX cur : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (i < INT_MAX) ” &&
  “ (Permutation input cur) ” &&
  “ (increasing (sublist ((0 : Int)) (i) (cur))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur) ((0 : Int))) <= (Znth (q) (cur) ((0 : Int))))) ”
  &&  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full a_pre n_pre cur)
) \/
(
forall (n_pre : Int) (input : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : ((Zlength (input)) = n_pre)) ,
  TT && emp 
|--
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (0 : Int))) ∧ ((0 : Int) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (input) ((0 : Int))) <= (Znth (q) (input) ((0 : Int))))) ” &&
  “ (increasing (sublist ((0 : Int)) ((0 : Int)) (input))) ” &&
  “ (Permutation input input) ”
  &&  emp
)

noncomputable def optimized_selection_sort_entail_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : ((Zlength (input)) = n_pre)) ,
  forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (0 : Int))) ∧ ((0 : Int) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (input) ((0 : Int))) <= (Znth (q) (input) ((0 : Int)))))

noncomputable def optimized_selection_sort_entail_wit_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : ((Zlength (input)) = n_pre)) ,
  (increasing (sublist ((0 : Int)) ((0 : Int)) (input)))

noncomputable def optimized_selection_sort_entail_wit_1_split_goal_3 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : ((Zlength (input)) = n_pre)) ,
  (Permutation input input)

noncomputable def optimized_selection_sort_entail_wit_2 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i_2 : Int) (cur_2 : (List Int)) (PreH1 : ((i_2 + 1) < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (cur_2)) = n_pre)) (PreH6 : ((0 : Int) <= i_2)) (PreH7 : (i_2 <= n_pre)) (PreH8 : (i_2 < INT_MAX)) (PreH9 : (Permutation input cur_2)) (PreH10 : (increasing (sublist ((0 : Int)) (i_2) (cur_2)))) (PreH11 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < i_2)) ∧ (i_2 <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (cur_2) ((0 : Int))) <= (Znth (q_2) (cur_2) ((0 : Int)))))) ,
  ((( &( "j" ) )) # Int |-> ((i_2 + 1)))
  ** ((( &( "min_index" ) )) # Int |-> (i_2))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_2))
  ** (intArray.full a_pre n_pre cur_2)
|--
  EX j : Int, EX min_index : Int, EX i : Int, EX cur : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ ((i + 1) < n_pre) ” &&
  “ (i <= min_index) ” &&
  “ (min_index < j) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (Permutation input cur) ” &&
  “ (increasing (sublist ((0 : Int)) (i) (cur))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur) ((0 : Int))) <= (Znth (q) (cur) ((0 : Int))))) ” &&
  “ (selection_minimum (sublist (i) (j) (cur)) (Znth (min_index) (cur) ((0 : Int)))) ”
  &&  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "min_index" ) )) # Int |-> (min_index))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full a_pre n_pre cur)
) \/
(
forall (n_pre : Int) (input : (List Int)) (i_2 : Int) (cur_2 : (List Int)) (PreH1 : ((i_2 + 1) < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (cur_2)) = n_pre)) (PreH6 : ((0 : Int) <= i_2)) (PreH7 : (i_2 <= n_pre)) (PreH8 : (i_2 < INT_MAX)) (PreH9 : (Permutation input cur_2)) (PreH10 : (increasing (sublist ((0 : Int)) (i_2) (cur_2)))) (PreH11 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < i_2)) ∧ (i_2 <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (cur_2) ((0 : Int))) <= (Znth (q_2) (cur_2) ((0 : Int)))))) ,
  TT && emp 
|--
  “ (selection_minimum (sublist (i_2) ((i_2 + 1)) (cur_2)) (Znth (i_2) (cur_2) ((0 : Int)))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i_2)) ∧ (i_2 <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur_2) ((0 : Int))) <= (Znth (q) (cur_2) ((0 : Int))))) ”
  &&  emp
)

noncomputable def optimized_selection_sort_entail_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (i_2 : Int) (cur_2 : (List Int)) (PreH1 : ((i_2 + 1) < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (cur_2)) = n_pre)) (PreH6 : ((0 : Int) <= i_2)) (PreH7 : (i_2 <= n_pre)) (PreH8 : (i_2 < INT_MAX)) (PreH9 : (Permutation input cur_2)) (PreH10 : (increasing (sublist ((0 : Int)) (i_2) (cur_2)))) (PreH11 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < i_2)) ∧ (i_2 <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (cur_2) ((0 : Int))) <= (Znth (q_2) (cur_2) ((0 : Int)))))) ,
  (selection_minimum (sublist (i_2) ((i_2 + 1)) (cur_2)) (Znth (i_2) (cur_2) ((0 : Int))))

noncomputable def optimized_selection_sort_entail_wit_2_split_goal_2 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (i_2 : Int) (cur_2 : (List Int)) (PreH1 : ((i_2 + 1) < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (cur_2)) = n_pre)) (PreH6 : ((0 : Int) <= i_2)) (PreH7 : (i_2 <= n_pre)) (PreH8 : (i_2 < INT_MAX)) (PreH9 : (Permutation input cur_2)) (PreH10 : (increasing (sublist ((0 : Int)) (i_2) (cur_2)))) (PreH11 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < i_2)) ∧ (i_2 <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (cur_2) ((0 : Int))) <= (Znth (q_2) (cur_2) ((0 : Int)))))) ,
  forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i_2)) ∧ (i_2 <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur_2) ((0 : Int))) <= (Znth (q) (cur_2) ((0 : Int)))))

noncomputable def optimized_selection_sort_entail_wit_3_1 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (j_2 : Int) (min_index_2 : Int) (i_2 : Int) (cur_2 : (List Int)) (PreH1 : ((Znth j_2 cur_2 (0 : Int)) < (Znth min_index_2 cur_2 (0 : Int)))) (PreH2 : (j_2 < n_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : ((Zlength (cur_2)) = n_pre)) (PreH7 : ((0 : Int) <= i_2)) (PreH8 : ((i_2 + 1) < n_pre)) (PreH9 : (i_2 <= min_index_2)) (PreH10 : (min_index_2 < j_2)) (PreH11 : ((i_2 + 1) <= j_2)) (PreH12 : (j_2 <= n_pre)) (PreH13 : (Permutation input cur_2)) (PreH14 : (increasing (sublist ((0 : Int)) (i_2) (cur_2)))) (PreH15 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i_2)) ∧ (i_2 <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur_2) ((0 : Int))) <= (Znth (q) (cur_2) ((0 : Int)))))) (PreH16 : (selection_minimum (sublist (i_2) (j_2) (cur_2)) (Znth (min_index_2) (cur_2) ((0 : Int))))) ,
  (intArray.full a_pre n_pre cur_2)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_2))
  ** ((( &( "min_index" ) )) # Int |-> (j_2))
  ** ((( &( "j" ) )) # Int |-> ((j_2 + 1)))
|--
  EX j : Int, EX min_index : Int, EX i : Int, EX cur : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ ((i + 1) < n_pre) ” &&
  “ (i <= min_index) ” &&
  “ (min_index < j) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (Permutation input cur) ” &&
  “ (increasing (sublist ((0 : Int)) (i) (cur))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur) ((0 : Int))) <= (Znth (q) (cur) ((0 : Int))))) ” &&
  “ (selection_minimum (sublist (i) (j) (cur)) (Znth (min_index) (cur) ((0 : Int)))) ”
  &&  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "min_index" ) )) # Int |-> (min_index))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full a_pre n_pre cur)
) \/
(
forall (n_pre : Int) (input : (List Int)) (j_2 : Int) (min_index_2 : Int) (i_2 : Int) (cur_2 : (List Int)) (PreH1 : ((Znth j_2 cur_2 (0 : Int)) < (Znth min_index_2 cur_2 (0 : Int)))) (PreH2 : (j_2 < n_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : ((Zlength (cur_2)) = n_pre)) (PreH7 : ((0 : Int) <= i_2)) (PreH8 : ((i_2 + 1) < n_pre)) (PreH9 : (i_2 <= min_index_2)) (PreH10 : (min_index_2 < j_2)) (PreH11 : ((i_2 + 1) <= j_2)) (PreH12 : (j_2 <= n_pre)) (PreH13 : (Permutation input cur_2)) (PreH14 : (increasing (sublist ((0 : Int)) (i_2) (cur_2)))) (PreH15 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i_2)) ∧ (i_2 <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur_2) ((0 : Int))) <= (Znth (q) (cur_2) ((0 : Int)))))) (PreH16 : (selection_minimum (sublist (i_2) (j_2) (cur_2)) (Znth (min_index_2) (cur_2) ((0 : Int))))) ,
  TT && emp 
|--
  “ (selection_minimum (sublist (i_2) ((j_2 + 1)) (cur_2)) (Znth (j_2) (cur_2) ((0 : Int)))) ”
  &&  emp
)

noncomputable def optimized_selection_sort_entail_wit_3_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (j_2 : Int) (min_index_2 : Int) (i_2 : Int) (cur_2 : (List Int)) (PreH1 : ((Znth j_2 cur_2 (0 : Int)) < (Znth min_index_2 cur_2 (0 : Int)))) (PreH2 : (j_2 < n_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : ((Zlength (cur_2)) = n_pre)) (PreH7 : ((0 : Int) <= i_2)) (PreH8 : ((i_2 + 1) < n_pre)) (PreH9 : (i_2 <= min_index_2)) (PreH10 : (min_index_2 < j_2)) (PreH11 : ((i_2 + 1) <= j_2)) (PreH12 : (j_2 <= n_pre)) (PreH13 : (Permutation input cur_2)) (PreH14 : (increasing (sublist ((0 : Int)) (i_2) (cur_2)))) (PreH15 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i_2)) ∧ (i_2 <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur_2) ((0 : Int))) <= (Znth (q) (cur_2) ((0 : Int)))))) (PreH16 : (selection_minimum (sublist (i_2) (j_2) (cur_2)) (Znth (min_index_2) (cur_2) ((0 : Int))))) ,
  (selection_minimum (sublist (i_2) ((j_2 + 1)) (cur_2)) (Znth (j_2) (cur_2) ((0 : Int))))

noncomputable def optimized_selection_sort_entail_wit_3_2 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (j_2 : Int) (min_index_2 : Int) (i_2 : Int) (cur_2 : (List Int)) (PreH1 : ((Znth j_2 cur_2 (0 : Int)) >= (Znth min_index_2 cur_2 (0 : Int)))) (PreH2 : (j_2 < n_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : ((Zlength (cur_2)) = n_pre)) (PreH7 : ((0 : Int) <= i_2)) (PreH8 : ((i_2 + 1) < n_pre)) (PreH9 : (i_2 <= min_index_2)) (PreH10 : (min_index_2 < j_2)) (PreH11 : ((i_2 + 1) <= j_2)) (PreH12 : (j_2 <= n_pre)) (PreH13 : (Permutation input cur_2)) (PreH14 : (increasing (sublist ((0 : Int)) (i_2) (cur_2)))) (PreH15 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i_2)) ∧ (i_2 <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur_2) ((0 : Int))) <= (Znth (q) (cur_2) ((0 : Int)))))) (PreH16 : (selection_minimum (sublist (i_2) (j_2) (cur_2)) (Znth (min_index_2) (cur_2) ((0 : Int))))) ,
  (intArray.full a_pre n_pre cur_2)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_2))
  ** ((( &( "min_index" ) )) # Int |-> (min_index_2))
  ** ((( &( "j" ) )) # Int |-> ((j_2 + 1)))
|--
  EX j : Int, EX min_index : Int, EX i : Int, EX cur : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ ((i + 1) < n_pre) ” &&
  “ (i <= min_index) ” &&
  “ (min_index < j) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (Permutation input cur) ” &&
  “ (increasing (sublist ((0 : Int)) (i) (cur))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur) ((0 : Int))) <= (Znth (q) (cur) ((0 : Int))))) ” &&
  “ (selection_minimum (sublist (i) (j) (cur)) (Znth (min_index) (cur) ((0 : Int)))) ”
  &&  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "min_index" ) )) # Int |-> (min_index))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full a_pre n_pre cur)
) \/
(
forall (n_pre : Int) (input : (List Int)) (j_2 : Int) (min_index_2 : Int) (i_2 : Int) (cur_2 : (List Int)) (PreH1 : ((Znth j_2 cur_2 (0 : Int)) >= (Znth min_index_2 cur_2 (0 : Int)))) (PreH2 : (j_2 < n_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : ((Zlength (cur_2)) = n_pre)) (PreH7 : ((0 : Int) <= i_2)) (PreH8 : ((i_2 + 1) < n_pre)) (PreH9 : (i_2 <= min_index_2)) (PreH10 : (min_index_2 < j_2)) (PreH11 : ((i_2 + 1) <= j_2)) (PreH12 : (j_2 <= n_pre)) (PreH13 : (Permutation input cur_2)) (PreH14 : (increasing (sublist ((0 : Int)) (i_2) (cur_2)))) (PreH15 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i_2)) ∧ (i_2 <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur_2) ((0 : Int))) <= (Znth (q) (cur_2) ((0 : Int)))))) (PreH16 : (selection_minimum (sublist (i_2) (j_2) (cur_2)) (Znth (min_index_2) (cur_2) ((0 : Int))))) ,
  TT && emp 
|--
  “ (selection_minimum (sublist (i_2) ((j_2 + 1)) (cur_2)) (Znth (min_index_2) (cur_2) ((0 : Int)))) ”
  &&  emp
)

noncomputable def optimized_selection_sort_entail_wit_3_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (j_2 : Int) (min_index_2 : Int) (i_2 : Int) (cur_2 : (List Int)) (PreH1 : ((Znth j_2 cur_2 (0 : Int)) >= (Znth min_index_2 cur_2 (0 : Int)))) (PreH2 : (j_2 < n_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : ((Zlength (cur_2)) = n_pre)) (PreH7 : ((0 : Int) <= i_2)) (PreH8 : ((i_2 + 1) < n_pre)) (PreH9 : (i_2 <= min_index_2)) (PreH10 : (min_index_2 < j_2)) (PreH11 : ((i_2 + 1) <= j_2)) (PreH12 : (j_2 <= n_pre)) (PreH13 : (Permutation input cur_2)) (PreH14 : (increasing (sublist ((0 : Int)) (i_2) (cur_2)))) (PreH15 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i_2)) ∧ (i_2 <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur_2) ((0 : Int))) <= (Znth (q) (cur_2) ((0 : Int)))))) (PreH16 : (selection_minimum (sublist (i_2) (j_2) (cur_2)) (Znth (min_index_2) (cur_2) ((0 : Int))))) ,
  (selection_minimum (sublist (i_2) ((j_2 + 1)) (cur_2)) (Znth (min_index_2) (cur_2) ((0 : Int))))

noncomputable def optimized_selection_sort_entail_wit_4_1 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (j : Int) (min_index : Int) (i_2 : Int) (cur_2 : (List Int)) (PreH1 : (min_index ≠ i_2)) (PreH2 : (j >= n_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : ((Zlength (cur_2)) = n_pre)) (PreH7 : ((0 : Int) <= i_2)) (PreH8 : ((i_2 + 1) < n_pre)) (PreH9 : (i_2 <= min_index)) (PreH10 : (min_index < j)) (PreH11 : ((i_2 + 1) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : (Permutation input cur_2)) (PreH14 : (increasing (sublist ((0 : Int)) (i_2) (cur_2)))) (PreH15 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < i_2)) ∧ (i_2 <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (cur_2) ((0 : Int))) <= (Znth (q_2) (cur_2) ((0 : Int)))))) (PreH16 : (selection_minimum (sublist (i_2) (j) (cur_2)) (Znth (min_index) (cur_2) ((0 : Int))))) ,
  (intArray.full a_pre n_pre (replace_Znth (min_index) ((Znth i_2 cur_2 (0 : Int))) ((replace_Znth (i_2) ((Znth min_index cur_2 (0 : Int))) (cur_2)))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> ((i_2 + 1)))
|--
  EX i : Int, EX cur : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (i < INT_MAX) ” &&
  “ (Permutation input cur) ” &&
  “ (increasing (sublist ((0 : Int)) (i) (cur))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur) ((0 : Int))) <= (Znth (q) (cur) ((0 : Int))))) ”
  &&  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full a_pre n_pre cur)
) \/
(
forall (n_pre : Int) (input : (List Int)) (j : Int) (min_index : Int) (i_2 : Int) (cur_2 : (List Int)) (PreH1 : ((Zlength ((replace_Znth (min_index) ((Znth i_2 cur_2 (0 : Int))) ((replace_Znth (i_2) ((Znth min_index cur_2 (0 : Int))) (cur_2)))))) = n_pre)) (PreH2 : (min_index ≠ i_2)) (PreH3 : (j >= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : ((Zlength (cur_2)) = n_pre)) (PreH8 : ((0 : Int) <= i_2)) (PreH9 : ((i_2 + 1) < n_pre)) (PreH10 : (i_2 <= min_index)) (PreH11 : (min_index < j)) (PreH12 : ((i_2 + 1) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : (Permutation input cur_2)) (PreH15 : (increasing (sublist ((0 : Int)) (i_2) (cur_2)))) (PreH16 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < i_2)) ∧ (i_2 <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (cur_2) ((0 : Int))) <= (Znth (q_2) (cur_2) ((0 : Int)))))) (PreH17 : (selection_minimum (sublist (i_2) (j) (cur_2)) (Znth (min_index) (cur_2) ((0 : Int))))) ,
  TT && emp 
|--
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (i_2 + 1))) ∧ ((i_2 + 1) <= q)) ∧ (q < n_pre)) -> ((Znth (p) ((replace_Znth (min_index) ((Znth i_2 cur_2 (0 : Int))) ((replace_Znth (i_2) ((Znth min_index cur_2 (0 : Int))) (cur_2))))) ((0 : Int))) <= (Znth (q) ((replace_Znth (min_index) ((Znth i_2 cur_2 (0 : Int))) ((replace_Znth (i_2) ((Znth min_index cur_2 (0 : Int))) (cur_2))))) ((0 : Int))))) ” &&
  “ (increasing (sublist ((0 : Int)) ((i_2 + 1)) ((replace_Znth (min_index) ((Znth i_2 cur_2 (0 : Int))) ((replace_Znth (i_2) ((Znth min_index cur_2 (0 : Int))) (cur_2))))))) ” &&
  “ (Permutation input (replace_Znth (min_index) ((Znth i_2 cur_2 (0 : Int))) ((replace_Znth (i_2) ((Znth min_index cur_2 (0 : Int))) (cur_2))))) ”
  &&  emp
)

noncomputable def optimized_selection_sort_entail_wit_4_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (j : Int) (min_index : Int) (i_2 : Int) (cur_2 : (List Int)) (PreH1 : ((Zlength ((replace_Znth (min_index) ((Znth i_2 cur_2 (0 : Int))) ((replace_Znth (i_2) ((Znth min_index cur_2 (0 : Int))) (cur_2)))))) = n_pre)) (PreH2 : (min_index ≠ i_2)) (PreH3 : (j >= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : ((Zlength (cur_2)) = n_pre)) (PreH8 : ((0 : Int) <= i_2)) (PreH9 : ((i_2 + 1) < n_pre)) (PreH10 : (i_2 <= min_index)) (PreH11 : (min_index < j)) (PreH12 : ((i_2 + 1) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : (Permutation input cur_2)) (PreH15 : (increasing (sublist ((0 : Int)) (i_2) (cur_2)))) (PreH16 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < i_2)) ∧ (i_2 <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (cur_2) ((0 : Int))) <= (Znth (q_2) (cur_2) ((0 : Int)))))) (PreH17 : (selection_minimum (sublist (i_2) (j) (cur_2)) (Znth (min_index) (cur_2) ((0 : Int))))) ,
  forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (i_2 + 1))) ∧ ((i_2 + 1) <= q)) ∧ (q < n_pre)) -> ((Znth (p) ((replace_Znth (min_index) ((Znth i_2 cur_2 (0 : Int))) ((replace_Znth (i_2) ((Znth min_index cur_2 (0 : Int))) (cur_2))))) ((0 : Int))) <= (Znth (q) ((replace_Znth (min_index) ((Znth i_2 cur_2 (0 : Int))) ((replace_Znth (i_2) ((Znth min_index cur_2 (0 : Int))) (cur_2))))) ((0 : Int)))))

noncomputable def optimized_selection_sort_entail_wit_4_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (j : Int) (min_index : Int) (i_2 : Int) (cur_2 : (List Int)) (PreH1 : ((Zlength ((replace_Znth (min_index) ((Znth i_2 cur_2 (0 : Int))) ((replace_Znth (i_2) ((Znth min_index cur_2 (0 : Int))) (cur_2)))))) = n_pre)) (PreH2 : (min_index ≠ i_2)) (PreH3 : (j >= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : ((Zlength (cur_2)) = n_pre)) (PreH8 : ((0 : Int) <= i_2)) (PreH9 : ((i_2 + 1) < n_pre)) (PreH10 : (i_2 <= min_index)) (PreH11 : (min_index < j)) (PreH12 : ((i_2 + 1) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : (Permutation input cur_2)) (PreH15 : (increasing (sublist ((0 : Int)) (i_2) (cur_2)))) (PreH16 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < i_2)) ∧ (i_2 <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (cur_2) ((0 : Int))) <= (Znth (q_2) (cur_2) ((0 : Int)))))) (PreH17 : (selection_minimum (sublist (i_2) (j) (cur_2)) (Znth (min_index) (cur_2) ((0 : Int))))) ,
  (increasing (sublist ((0 : Int)) ((i_2 + 1)) ((replace_Znth (min_index) ((Znth i_2 cur_2 (0 : Int))) ((replace_Znth (i_2) ((Znth min_index cur_2 (0 : Int))) (cur_2)))))))

noncomputable def optimized_selection_sort_entail_wit_4_1_split_goal_3 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (j : Int) (min_index : Int) (i_2 : Int) (cur_2 : (List Int)) (PreH1 : ((Zlength ((replace_Znth (min_index) ((Znth i_2 cur_2 (0 : Int))) ((replace_Znth (i_2) ((Znth min_index cur_2 (0 : Int))) (cur_2)))))) = n_pre)) (PreH2 : (min_index ≠ i_2)) (PreH3 : (j >= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : ((Zlength (cur_2)) = n_pre)) (PreH8 : ((0 : Int) <= i_2)) (PreH9 : ((i_2 + 1) < n_pre)) (PreH10 : (i_2 <= min_index)) (PreH11 : (min_index < j)) (PreH12 : ((i_2 + 1) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : (Permutation input cur_2)) (PreH15 : (increasing (sublist ((0 : Int)) (i_2) (cur_2)))) (PreH16 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < i_2)) ∧ (i_2 <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (cur_2) ((0 : Int))) <= (Znth (q_2) (cur_2) ((0 : Int)))))) (PreH17 : (selection_minimum (sublist (i_2) (j) (cur_2)) (Znth (min_index) (cur_2) ((0 : Int))))) ,
  (Permutation input (replace_Znth (min_index) ((Znth i_2 cur_2 (0 : Int))) ((replace_Znth (i_2) ((Znth min_index cur_2 (0 : Int))) (cur_2)))))

noncomputable def optimized_selection_sort_entail_wit_4_2 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (j : Int) (min_index : Int) (i_2 : Int) (cur_2 : (List Int)) (PreH1 : (min_index = i_2)) (PreH2 : (j >= n_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : ((Zlength (cur_2)) = n_pre)) (PreH7 : ((0 : Int) <= i_2)) (PreH8 : ((i_2 + 1) < n_pre)) (PreH9 : (i_2 <= min_index)) (PreH10 : (min_index < j)) (PreH11 : ((i_2 + 1) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : (Permutation input cur_2)) (PreH14 : (increasing (sublist ((0 : Int)) (i_2) (cur_2)))) (PreH15 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < i_2)) ∧ (i_2 <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (cur_2) ((0 : Int))) <= (Znth (q_2) (cur_2) ((0 : Int)))))) (PreH16 : (selection_minimum (sublist (i_2) (j) (cur_2)) (Znth (min_index) (cur_2) ((0 : Int))))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> ((i_2 + 1)))
  ** (intArray.full a_pre n_pre cur_2)
|--
  EX i : Int, EX cur : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (i < INT_MAX) ” &&
  “ (Permutation input cur) ” &&
  “ (increasing (sublist ((0 : Int)) (i) (cur))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur) ((0 : Int))) <= (Znth (q) (cur) ((0 : Int))))) ”
  &&  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full a_pre n_pre cur)
) \/
(
forall (n_pre : Int) (input : (List Int)) (j : Int) (min_index : Int) (i_2 : Int) (cur_2 : (List Int)) (PreH1 : (min_index = i_2)) (PreH2 : (j >= n_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : ((Zlength (cur_2)) = n_pre)) (PreH7 : ((0 : Int) <= i_2)) (PreH8 : ((i_2 + 1) < n_pre)) (PreH9 : (i_2 <= min_index)) (PreH10 : (min_index < j)) (PreH11 : ((i_2 + 1) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : (Permutation input cur_2)) (PreH14 : (increasing (sublist ((0 : Int)) (i_2) (cur_2)))) (PreH15 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < i_2)) ∧ (i_2 <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (cur_2) ((0 : Int))) <= (Znth (q_2) (cur_2) ((0 : Int)))))) (PreH16 : (selection_minimum (sublist (i_2) (j) (cur_2)) (Znth (min_index) (cur_2) ((0 : Int))))) ,
  TT && emp 
|--
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (i_2 + 1))) ∧ ((i_2 + 1) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur_2) ((0 : Int))) <= (Znth (q) (cur_2) ((0 : Int))))) ” &&
  “ (increasing (sublist ((0 : Int)) ((min_index + 1)) (cur_2))) ”
  &&  emp
)

noncomputable def optimized_selection_sort_entail_wit_4_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (j : Int) (min_index : Int) (i_2 : Int) (cur_2 : (List Int)) (PreH1 : (min_index = i_2)) (PreH2 : (j >= n_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : ((Zlength (cur_2)) = n_pre)) (PreH7 : ((0 : Int) <= i_2)) (PreH8 : ((i_2 + 1) < n_pre)) (PreH9 : (i_2 <= min_index)) (PreH10 : (min_index < j)) (PreH11 : ((i_2 + 1) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : (Permutation input cur_2)) (PreH14 : (increasing (sublist ((0 : Int)) (i_2) (cur_2)))) (PreH15 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < i_2)) ∧ (i_2 <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (cur_2) ((0 : Int))) <= (Znth (q_2) (cur_2) ((0 : Int)))))) (PreH16 : (selection_minimum (sublist (i_2) (j) (cur_2)) (Znth (min_index) (cur_2) ((0 : Int))))) ,
  forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (i_2 + 1))) ∧ ((i_2 + 1) <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur_2) ((0 : Int))) <= (Znth (q) (cur_2) ((0 : Int)))))

noncomputable def optimized_selection_sort_entail_wit_4_2_split_goal_2 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (j : Int) (min_index : Int) (i_2 : Int) (cur_2 : (List Int)) (PreH1 : (min_index = i_2)) (PreH2 : (j >= n_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : ((Zlength (cur_2)) = n_pre)) (PreH7 : ((0 : Int) <= i_2)) (PreH8 : ((i_2 + 1) < n_pre)) (PreH9 : (i_2 <= min_index)) (PreH10 : (min_index < j)) (PreH11 : ((i_2 + 1) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : (Permutation input cur_2)) (PreH14 : (increasing (sublist ((0 : Int)) (i_2) (cur_2)))) (PreH15 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < i_2)) ∧ (i_2 <= q_2)) ∧ (q_2 < n_pre)) -> ((Znth (p_2) (cur_2) ((0 : Int))) <= (Znth (q_2) (cur_2) ((0 : Int)))))) (PreH16 : (selection_minimum (sublist (i_2) (j) (cur_2)) (Znth (min_index) (cur_2) ((0 : Int))))) ,
  (increasing (sublist ((0 : Int)) ((min_index + 1)) (cur_2)))

noncomputable def optimized_selection_sort_return_wit_1 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (i : Int) (cur : (List Int)) (PreH1 : ((i + 1) >= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (cur)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (i < INT_MAX)) (PreH9 : (Permutation input cur)) (PreH10 : (increasing (sublist ((0 : Int)) (i) (cur)))) (PreH11 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur) ((0 : Int))) <= (Znth (q) (cur) ((0 : Int)))))) ,
  (intArray.full a_pre n_pre cur)
|--
  EX output : (List Int),
  “ (optimized_selection_sort_result input output) ”
  &&  (intArray.full a_pre n_pre output)
) \/
(
forall (n_pre : Int) (input : (List Int)) (i : Int) (cur : (List Int)) (PreH1 : ((i + 1) >= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (cur)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (i < INT_MAX)) (PreH9 : (Permutation input cur)) (PreH10 : (increasing (sublist ((0 : Int)) (i) (cur)))) (PreH11 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur) ((0 : Int))) <= (Znth (q) (cur) ((0 : Int)))))) ,
  TT && emp 
|--
  “ (optimized_selection_sort_result input cur) ”
  &&  emp
)

noncomputable def optimized_selection_sort_return_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (i : Int) (cur : (List Int)) (PreH1 : ((i + 1) >= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (cur)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (i < INT_MAX)) (PreH9 : (Permutation input cur)) (PreH10 : (increasing (sublist ((0 : Int)) (i) (cur)))) (PreH11 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur) ((0 : Int))) <= (Znth (q) (cur) ((0 : Int)))))) ,
  (optimized_selection_sort_result input cur)

noncomputable def optimized_selection_sort_partial_solve_wit_1 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (j : Int) (min_index : Int) (i : Int) (cur : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (cur)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : ((i + 1) < n_pre)) (PreH8 : (i <= min_index)) (PreH9 : (min_index < j)) (PreH10 : ((i + 1) <= j)) (PreH11 : (j <= n_pre)) (PreH12 : (Permutation input cur)) (PreH13 : (increasing (sublist ((0 : Int)) (i) (cur)))) (PreH14 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur) ((0 : Int))) <= (Znth (q) (cur) ((0 : Int)))))) (PreH15 : (selection_minimum (sublist (i) (j) (cur)) (Znth (min_index) (cur) ((0 : Int))))) ,
  (intArray.full a_pre n_pre cur)
|--
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ ((i + 1) < n_pre) ” &&
  “ (i <= min_index) ” &&
  “ (min_index < j) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (Permutation input cur) ” &&
  “ (increasing (sublist ((0 : Int)) (i) (cur))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur) ((0 : Int))) <= (Znth (q) (cur) ((0 : Int))))) ” &&
  “ (selection_minimum (sublist (i) (j) (cur)) (Znth (min_index) (cur) ((0 : Int)))) ”
  &&  (((a_pre + (j * sizeof(INT)))) # Int |-> ((Znth j cur (0 : Int))))
  ** (intArray.missing_i a_pre j (0 : Int) n_pre cur)

noncomputable def optimized_selection_sort_partial_solve_wit_2 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (j : Int) (min_index : Int) (i : Int) (cur : (List Int)) (PreH1 : (j < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (cur)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : ((i + 1) < n_pre)) (PreH8 : (i <= min_index)) (PreH9 : (min_index < j)) (PreH10 : ((i + 1) <= j)) (PreH11 : (j <= n_pre)) (PreH12 : (Permutation input cur)) (PreH13 : (increasing (sublist ((0 : Int)) (i) (cur)))) (PreH14 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur) ((0 : Int))) <= (Znth (q) (cur) ((0 : Int)))))) (PreH15 : (selection_minimum (sublist (i) (j) (cur)) (Znth (min_index) (cur) ((0 : Int))))) ,
  (intArray.full a_pre n_pre cur)
|--
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ ((i + 1) < n_pre) ” &&
  “ (i <= min_index) ” &&
  “ (min_index < j) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (Permutation input cur) ” &&
  “ (increasing (sublist ((0 : Int)) (i) (cur))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur) ((0 : Int))) <= (Znth (q) (cur) ((0 : Int))))) ” &&
  “ (selection_minimum (sublist (i) (j) (cur)) (Znth (min_index) (cur) ((0 : Int)))) ”
  &&  (((a_pre + (min_index * sizeof(INT)))) # Int |-> ((Znth min_index cur (0 : Int))))
  ** (intArray.missing_i a_pre min_index (0 : Int) n_pre cur)

noncomputable def optimized_selection_sort_partial_solve_wit_3 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (j : Int) (min_index : Int) (i : Int) (cur : (List Int)) (PreH1 : (min_index ≠ i)) (PreH2 : (j >= n_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : ((Zlength (cur)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : ((i + 1) < n_pre)) (PreH9 : (i <= min_index)) (PreH10 : (min_index < j)) (PreH11 : ((i + 1) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : (Permutation input cur)) (PreH14 : (increasing (sublist ((0 : Int)) (i) (cur)))) (PreH15 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur) ((0 : Int))) <= (Znth (q) (cur) ((0 : Int)))))) (PreH16 : (selection_minimum (sublist (i) (j) (cur)) (Znth (min_index) (cur) ((0 : Int))))) ,
  (intArray.full a_pre n_pre cur)
|--
  “ (min_index ≠ i) ” &&
  “ (j >= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ ((i + 1) < n_pre) ” &&
  “ (i <= min_index) ” &&
  “ (min_index < j) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (Permutation input cur) ” &&
  “ (increasing (sublist ((0 : Int)) (i) (cur))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur) ((0 : Int))) <= (Znth (q) (cur) ((0 : Int))))) ” &&
  “ (selection_minimum (sublist (i) (j) (cur)) (Znth (min_index) (cur) ((0 : Int)))) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i cur (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre cur)

noncomputable def optimized_selection_sort_partial_solve_wit_4 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (j : Int) (min_index : Int) (i : Int) (cur : (List Int)) (PreH1 : (min_index ≠ i)) (PreH2 : (j >= n_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : ((Zlength (cur)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : ((i + 1) < n_pre)) (PreH9 : (i <= min_index)) (PreH10 : (min_index < j)) (PreH11 : ((i + 1) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : (Permutation input cur)) (PreH14 : (increasing (sublist ((0 : Int)) (i) (cur)))) (PreH15 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur) ((0 : Int))) <= (Znth (q) (cur) ((0 : Int)))))) (PreH16 : (selection_minimum (sublist (i) (j) (cur)) (Znth (min_index) (cur) ((0 : Int))))) ,
  (intArray.full a_pre n_pre cur)
|--
  “ (min_index ≠ i) ” &&
  “ (j >= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ ((i + 1) < n_pre) ” &&
  “ (i <= min_index) ” &&
  “ (min_index < j) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (Permutation input cur) ” &&
  “ (increasing (sublist ((0 : Int)) (i) (cur))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur) ((0 : Int))) <= (Znth (q) (cur) ((0 : Int))))) ” &&
  “ (selection_minimum (sublist (i) (j) (cur)) (Znth (min_index) (cur) ((0 : Int)))) ”
  &&  (((a_pre + (min_index * sizeof(INT)))) # Int |-> ((Znth min_index cur (0 : Int))))
  ** (intArray.missing_i a_pre min_index (0 : Int) n_pre cur)

noncomputable def optimized_selection_sort_partial_solve_wit_5 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (j : Int) (min_index : Int) (i : Int) (cur : (List Int)) (PreH1 : (min_index ≠ i)) (PreH2 : (j >= n_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : ((Zlength (cur)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : ((i + 1) < n_pre)) (PreH9 : (i <= min_index)) (PreH10 : (min_index < j)) (PreH11 : ((i + 1) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : (Permutation input cur)) (PreH14 : (increasing (sublist ((0 : Int)) (i) (cur)))) (PreH15 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur) ((0 : Int))) <= (Znth (q) (cur) ((0 : Int)))))) (PreH16 : (selection_minimum (sublist (i) (j) (cur)) (Znth (min_index) (cur) ((0 : Int))))) ,
  (intArray.full a_pre n_pre cur)
|--
  “ (min_index ≠ i) ” &&
  “ (j >= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ ((i + 1) < n_pre) ” &&
  “ (i <= min_index) ” &&
  “ (min_index < j) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (Permutation input cur) ” &&
  “ (increasing (sublist ((0 : Int)) (i) (cur))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur) ((0 : Int))) <= (Znth (q) (cur) ((0 : Int))))) ” &&
  “ (selection_minimum (sublist (i) (j) (cur)) (Znth (min_index) (cur) ((0 : Int)))) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i a_pre i (0 : Int) n_pre cur)

noncomputable def optimized_selection_sort_partial_solve_wit_6 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (j : Int) (min_index : Int) (i : Int) (cur : (List Int)) (PreH1 : (min_index ≠ i)) (PreH2 : (j >= n_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : ((Zlength (cur)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : ((i + 1) < n_pre)) (PreH9 : (i <= min_index)) (PreH10 : (min_index < j)) (PreH11 : ((i + 1) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : (Permutation input cur)) (PreH14 : (increasing (sublist ((0 : Int)) (i) (cur)))) (PreH15 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur) ((0 : Int))) <= (Znth (q) (cur) ((0 : Int)))))) (PreH16 : (selection_minimum (sublist (i) (j) (cur)) (Znth (min_index) (cur) ((0 : Int))))) ,
  (intArray.full a_pre n_pre (replace_Znth (i) ((Znth min_index cur (0 : Int))) (cur)))
|--
  “ (min_index ≠ i) ” &&
  “ (j >= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ ((i + 1) < n_pre) ” &&
  “ (i <= min_index) ” &&
  “ (min_index < j) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (Permutation input cur) ” &&
  “ (increasing (sublist ((0 : Int)) (i) (cur))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < n_pre)) -> ((Znth (p) (cur) ((0 : Int))) <= (Znth (q) (cur) ((0 : Int))))) ” &&
  “ (selection_minimum (sublist (i) (j) (cur)) (Znth (min_index) (cur) ((0 : Int)))) ”
  &&  (((a_pre + (min_index * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i a_pre min_index (0 : Int) n_pre (replace_Znth (i) ((Znth min_index cur (0 : Int))) (cur)))


structure VC_Correct : Type where
  proof_of_optimized_selection_sort_safety_wit_1 : optimized_selection_sort_safety_wit_1
  proof_of_optimized_selection_sort_safety_wit_2 : optimized_selection_sort_safety_wit_2
  proof_of_optimized_selection_sort_safety_wit_3 : optimized_selection_sort_safety_wit_3
  proof_of_optimized_selection_sort_safety_wit_4 : optimized_selection_sort_safety_wit_4
  proof_of_optimized_selection_sort_safety_wit_5 : optimized_selection_sort_safety_wit_5
  proof_of_optimized_selection_sort_safety_wit_6 : optimized_selection_sort_safety_wit_6
  proof_of_optimized_selection_sort_safety_wit_7 : optimized_selection_sort_safety_wit_7
  proof_of_optimized_selection_sort_safety_wit_8 : optimized_selection_sort_safety_wit_8
  proof_of_optimized_selection_sort_safety_wit_9 : optimized_selection_sort_safety_wit_9
  proof_of_optimized_selection_sort_partial_solve_wit_1 : optimized_selection_sort_partial_solve_wit_1
  proof_of_optimized_selection_sort_partial_solve_wit_2 : optimized_selection_sort_partial_solve_wit_2
  proof_of_optimized_selection_sort_partial_solve_wit_3 : optimized_selection_sort_partial_solve_wit_3
  proof_of_optimized_selection_sort_partial_solve_wit_4 : optimized_selection_sort_partial_solve_wit_4
  proof_of_optimized_selection_sort_partial_solve_wit_5 : optimized_selection_sort_partial_solve_wit_5
  proof_of_optimized_selection_sort_partial_solve_wit_6 : optimized_selection_sort_partial_solve_wit_6
  proof_of_optimized_selection_sort_entail_wit_1 : optimized_selection_sort_entail_wit_1
  proof_of_optimized_selection_sort_entail_wit_2 : optimized_selection_sort_entail_wit_2
  proof_of_optimized_selection_sort_entail_wit_3_1 : optimized_selection_sort_entail_wit_3_1
  proof_of_optimized_selection_sort_entail_wit_3_2 : optimized_selection_sort_entail_wit_3_2
  proof_of_optimized_selection_sort_entail_wit_4_1 : optimized_selection_sort_entail_wit_4_1
  proof_of_optimized_selection_sort_entail_wit_4_2 : optimized_selection_sort_entail_wit_4_2
  proof_of_optimized_selection_sort_return_wit_1 : optimized_selection_sort_return_wit_1

end SimpleC.EE.LLM_bench.Algorithms.optimized_selection_sort.optimized_selection_sort_goal
