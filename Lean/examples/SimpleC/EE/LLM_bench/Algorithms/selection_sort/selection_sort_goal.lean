import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.selection_sort.selection_sort_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.selection_sort.selection_sort_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance selection_sort_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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
  forall (l : (List Int)) (nums_pre : Int) (numsSize_pre : Int) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 50000)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** (intArray.full nums_pre numsSize_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def sortArray_safety_wit_2 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (numsSize_pre : Int) (a : (List Int)) (i : Int) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= numsSize_pre)) (PreH6 : (Permutation l a)) (PreH7 : (increasing (sublist ((0 : Int)) (i) (a)))) (PreH8 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < numsSize_pre)) -> ((Znth p a (0 : Int)) <= (Znth q a (0 : Int))))) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full nums_pre numsSize_pre a)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def sortArray_safety_wit_3 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (numsSize_pre : Int) (a : (List Int)) (i : Int) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= numsSize_pre)) (PreH6 : (Permutation l a)) (PreH7 : (increasing (sublist ((0 : Int)) (i) (a)))) (PreH8 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < numsSize_pre)) -> ((Znth p a (0 : Int)) <= (Znth q a (0 : Int))))) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full nums_pre numsSize_pre a)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def sortArray_safety_wit_4 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (numsSize_pre : Int) (a : (List Int)) (j : Int) (i : Int) (PreH1 : ((Znth j a (0 : Int)) < (Znth i a (0 : Int)))) (PreH2 : (j < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : ((i + 1) <= j)) (PreH8 : (j <= numsSize_pre)) (PreH9 : (Permutation l a)) (PreH10 : (increasing (sublist ((0 : Int)) (i) (a)))) (PreH11 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < numsSize_pre)) -> ((Znth p a (0 : Int)) <= (Znth q a (0 : Int))))) (PreH12 : (selection_minimum (sublist (i) (j) (a)) (Znth i a (0 : Int)))) ,
  (intArray.full nums_pre numsSize_pre (replace_Znth (j) ((Znth i a (0 : Int))) ((replace_Znth (i) ((Znth j a (0 : Int))) (a)))))
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def sortArray_safety_wit_5 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (numsSize_pre : Int) (a : (List Int)) (j : Int) (i : Int) (PreH1 : ((Znth j a (0 : Int)) >= (Znth i a (0 : Int)))) (PreH2 : (j < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : ((i + 1) <= j)) (PreH8 : (j <= numsSize_pre)) (PreH9 : (Permutation l a)) (PreH10 : (increasing (sublist ((0 : Int)) (i) (a)))) (PreH11 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < numsSize_pre)) -> ((Znth p a (0 : Int)) <= (Znth q a (0 : Int))))) (PreH12 : (selection_minimum (sublist (i) (j) (a)) (Znth i a (0 : Int)))) ,
  (intArray.full nums_pre numsSize_pre a)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def sortArray_safety_wit_6 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (numsSize_pre : Int) (a : (List Int)) (j : Int) (i : Int) (PreH1 : (j >= numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < numsSize_pre)) (PreH6 : ((i + 1) <= j)) (PreH7 : (j <= numsSize_pre)) (PreH8 : (Permutation l a)) (PreH9 : (increasing (sublist ((0 : Int)) (i) (a)))) (PreH10 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < numsSize_pre)) -> ((Znth p a (0 : Int)) <= (Znth q a (0 : Int))))) (PreH11 : (selection_minimum (sublist (i) (j) (a)) (Znth i a (0 : Int)))) ,
  ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full nums_pre numsSize_pre a)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def sortArray_entail_wit_1 : Prop :=
  (
forall (l : (List Int)) (nums_pre : Int) (numsSize_pre : Int) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 50000)) ,
  ((( &( "i" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** (intArray.full nums_pre numsSize_pre l)
|--
  EX a : (List Int), EX i : Int,
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= numsSize_pre) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((0 : Int)) (i) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < numsSize_pre)) -> ((Znth p a (0 : Int)) <= (Znth q a (0 : Int)))) ”
  &&  ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full nums_pre numsSize_pre a)
) \/
(
forall (l : (List Int)) (numsSize_pre : Int) (PreH1 : ((Zlength (l)) = numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) ,
  TT && emp 
|--
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (0 : Int))) ∧ ((0 : Int) <= q)) ∧ (q < numsSize_pre)) -> ((Znth p l (0 : Int)) <= (Znth q l (0 : Int)))) ” &&
  “ (increasing (sublist ((0 : Int)) ((0 : Int)) (l))) ” &&
  “ (Permutation l l) ”
  &&  emp
)

noncomputable def sortArray_entail_wit_1_split_goal_1 : Prop :=
  forall (l : (List Int)) (numsSize_pre : Int) (PreH1 : ((Zlength (l)) = numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) ,
  forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (0 : Int))) ∧ ((0 : Int) <= q)) ∧ (q < numsSize_pre)) -> ((Znth p l (0 : Int)) <= (Znth q l (0 : Int))))

noncomputable def sortArray_entail_wit_1_split_goal_2 : Prop :=
  forall (l : (List Int)) (numsSize_pre : Int) (PreH1 : ((Zlength (l)) = numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) ,
  (increasing (sublist ((0 : Int)) ((0 : Int)) (l)))

noncomputable def sortArray_entail_wit_1_split_goal_3 : Prop :=
  forall (l : (List Int)) (numsSize_pre : Int) (PreH1 : ((Zlength (l)) = numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) ,
  (Permutation l l)

noncomputable def sortArray_entail_wit_2 : Prop :=
  (
forall (l : (List Int)) (nums_pre : Int) (numsSize_pre : Int) (a_2 : (List Int)) (i_2 : Int) (PreH1 : (i_2 < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 <= numsSize_pre)) (PreH6 : (Permutation l a_2)) (PreH7 : (increasing (sublist ((0 : Int)) (i_2) (a_2)))) (PreH8 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < i_2)) ∧ (i_2 <= q_2)) ∧ (q_2 < numsSize_pre)) -> ((Znth p_2 a_2 (0 : Int)) <= (Znth q_2 a_2 (0 : Int))))) ,
  ((( &( "j" ) )) # Int |-> ((i_2 + 1)))
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i_2))
  ** (intArray.full nums_pre numsSize_pre a_2)
|--
  EX a : (List Int), EX j : Int, EX i : Int,
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < numsSize_pre) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= numsSize_pre) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((0 : Int)) (i) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < numsSize_pre)) -> ((Znth p a (0 : Int)) <= (Znth q a (0 : Int)))) ” &&
  “ (selection_minimum (sublist (i) (j) (a)) (Znth i a (0 : Int))) ”
  &&  ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full nums_pre numsSize_pre a)
) \/
(
forall (l : (List Int)) (numsSize_pre : Int) (a_2 : (List Int)) (i_2 : Int) (PreH1 : ((Zlength (a_2)) = numsSize_pre)) (PreH2 : (i_2 < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : ((0 : Int) <= i_2)) (PreH6 : (i_2 <= numsSize_pre)) (PreH7 : (Permutation l a_2)) (PreH8 : (increasing (sublist ((0 : Int)) (i_2) (a_2)))) (PreH9 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < i_2)) ∧ (i_2 <= q_2)) ∧ (q_2 < numsSize_pre)) -> ((Znth p_2 a_2 (0 : Int)) <= (Znth q_2 a_2 (0 : Int))))) ,
  TT && emp 
|--
  “ (selection_minimum (sublist (i_2) ((i_2 + 1)) (a_2)) (Znth i_2 a_2 (0 : Int))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i_2)) ∧ (i_2 <= q)) ∧ (q < numsSize_pre)) -> ((Znth p a_2 (0 : Int)) <= (Znth q a_2 (0 : Int)))) ”
  &&  emp
)

noncomputable def sortArray_entail_wit_2_split_goal_1 : Prop :=
  forall (l : (List Int)) (numsSize_pre : Int) (a_2 : (List Int)) (i_2 : Int) (PreH1 : ((Zlength (a_2)) = numsSize_pre)) (PreH2 : (i_2 < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : ((0 : Int) <= i_2)) (PreH6 : (i_2 <= numsSize_pre)) (PreH7 : (Permutation l a_2)) (PreH8 : (increasing (sublist ((0 : Int)) (i_2) (a_2)))) (PreH9 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < i_2)) ∧ (i_2 <= q_2)) ∧ (q_2 < numsSize_pre)) -> ((Znth p_2 a_2 (0 : Int)) <= (Znth q_2 a_2 (0 : Int))))) ,
  (selection_minimum (sublist (i_2) ((i_2 + 1)) (a_2)) (Znth i_2 a_2 (0 : Int)))

noncomputable def sortArray_entail_wit_2_split_goal_2 : Prop :=
  forall (l : (List Int)) (numsSize_pre : Int) (a_2 : (List Int)) (i_2 : Int) (PreH1 : ((Zlength (a_2)) = numsSize_pre)) (PreH2 : (i_2 < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : ((0 : Int) <= i_2)) (PreH6 : (i_2 <= numsSize_pre)) (PreH7 : (Permutation l a_2)) (PreH8 : (increasing (sublist ((0 : Int)) (i_2) (a_2)))) (PreH9 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < i_2)) ∧ (i_2 <= q_2)) ∧ (q_2 < numsSize_pre)) -> ((Znth p_2 a_2 (0 : Int)) <= (Znth q_2 a_2 (0 : Int))))) ,
  forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i_2)) ∧ (i_2 <= q)) ∧ (q < numsSize_pre)) -> ((Znth p a_2 (0 : Int)) <= (Znth q a_2 (0 : Int))))

noncomputable def sortArray_entail_wit_3_1 : Prop :=
  (
forall (l : (List Int)) (nums_pre : Int) (numsSize_pre : Int) (a_2 : (List Int)) (j_2 : Int) (i_2 : Int) (PreH1 : ((Znth j_2 a_2 (0 : Int)) < (Znth i_2 a_2 (0 : Int)))) (PreH2 : (j_2 < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : ((0 : Int) <= i_2)) (PreH6 : (i_2 < numsSize_pre)) (PreH7 : ((i_2 + 1) <= j_2)) (PreH8 : (j_2 <= numsSize_pre)) (PreH9 : (Permutation l a_2)) (PreH10 : (increasing (sublist ((0 : Int)) (i_2) (a_2)))) (PreH11 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i_2)) ∧ (i_2 <= q)) ∧ (q < numsSize_pre)) -> ((Znth p a_2 (0 : Int)) <= (Znth q a_2 (0 : Int))))) (PreH12 : (selection_minimum (sublist (i_2) (j_2) (a_2)) (Znth i_2 a_2 (0 : Int)))) ,
  (intArray.full nums_pre numsSize_pre (replace_Znth (j_2) ((Znth i_2 a_2 (0 : Int))) ((replace_Znth (i_2) ((Znth j_2 a_2 (0 : Int))) (a_2)))))
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i_2))
  ** ((( &( "j" ) )) # Int |-> ((j_2 + 1)))
|--
  EX a : (List Int), EX j : Int, EX i : Int,
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < numsSize_pre) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= numsSize_pre) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((0 : Int)) (i) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < numsSize_pre)) -> ((Znth p a (0 : Int)) <= (Znth q a (0 : Int)))) ” &&
  “ (selection_minimum (sublist (i) (j) (a)) (Znth i a (0 : Int))) ”
  &&  ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full nums_pre numsSize_pre a)
) \/
(
forall (l : (List Int)) (numsSize_pre : Int) (a_2 : (List Int)) (j_2 : Int) (i_2 : Int) (PreH1 : ((Zlength ((replace_Znth (j_2) ((Znth i_2 a_2 (0 : Int))) ((replace_Znth (i_2) ((Znth j_2 a_2 (0 : Int))) (a_2)))))) = numsSize_pre)) (PreH2 : ((Znth j_2 a_2 (0 : Int)) < (Znth i_2 a_2 (0 : Int)))) (PreH3 : (j_2 < numsSize_pre)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 50000)) (PreH6 : ((0 : Int) <= i_2)) (PreH7 : (i_2 < numsSize_pre)) (PreH8 : ((i_2 + 1) <= j_2)) (PreH9 : (j_2 <= numsSize_pre)) (PreH10 : (Permutation l a_2)) (PreH11 : (increasing (sublist ((0 : Int)) (i_2) (a_2)))) (PreH12 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i_2)) ∧ (i_2 <= q)) ∧ (q < numsSize_pre)) -> ((Znth p a_2 (0 : Int)) <= (Znth q a_2 (0 : Int))))) (PreH13 : (selection_minimum (sublist (i_2) (j_2) (a_2)) (Znth i_2 a_2 (0 : Int)))) ,
  TT && emp 
|--
  “ (selection_minimum (sublist (i_2) ((j_2 + 1)) ((replace_Znth (j_2) ((Znth i_2 a_2 (0 : Int))) ((replace_Znth (i_2) ((Znth j_2 a_2 (0 : Int))) (a_2)))))) (Znth i_2 (replace_Znth (j_2) ((Znth i_2 a_2 (0 : Int))) ((replace_Znth (i_2) ((Znth j_2 a_2 (0 : Int))) (a_2)))) (0 : Int))) ” &&
  “ (increasing (sublist ((0 : Int)) (i_2) ((replace_Znth (j_2) ((Znth i_2 a_2 (0 : Int))) ((replace_Znth (i_2) ((Znth j_2 a_2 (0 : Int))) (a_2))))))) ” &&
  “ (Permutation l (replace_Znth (j_2) ((Znth i_2 a_2 (0 : Int))) ((replace_Znth (i_2) ((Znth j_2 a_2 (0 : Int))) (a_2))))) ”
  &&  emp
)

noncomputable def sortArray_entail_wit_3_1_split_goal_1 : Prop :=
  forall (l : (List Int)) (numsSize_pre : Int) (a_2 : (List Int)) (j_2 : Int) (i_2 : Int) (PreH1 : ((Zlength ((replace_Znth (j_2) ((Znth i_2 a_2 (0 : Int))) ((replace_Znth (i_2) ((Znth j_2 a_2 (0 : Int))) (a_2)))))) = numsSize_pre)) (PreH2 : ((Znth j_2 a_2 (0 : Int)) < (Znth i_2 a_2 (0 : Int)))) (PreH3 : (j_2 < numsSize_pre)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 50000)) (PreH6 : ((0 : Int) <= i_2)) (PreH7 : (i_2 < numsSize_pre)) (PreH8 : ((i_2 + 1) <= j_2)) (PreH9 : (j_2 <= numsSize_pre)) (PreH10 : (Permutation l a_2)) (PreH11 : (increasing (sublist ((0 : Int)) (i_2) (a_2)))) (PreH12 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i_2)) ∧ (i_2 <= q)) ∧ (q < numsSize_pre)) -> ((Znth p a_2 (0 : Int)) <= (Znth q a_2 (0 : Int))))) (PreH13 : (selection_minimum (sublist (i_2) (j_2) (a_2)) (Znth i_2 a_2 (0 : Int)))) ,
  (selection_minimum (sublist (i_2) ((j_2 + 1)) ((replace_Znth (j_2) ((Znth i_2 a_2 (0 : Int))) ((replace_Znth (i_2) ((Znth j_2 a_2 (0 : Int))) (a_2)))))) (Znth i_2 (replace_Znth (j_2) ((Znth i_2 a_2 (0 : Int))) ((replace_Znth (i_2) ((Znth j_2 a_2 (0 : Int))) (a_2)))) (0 : Int)))

noncomputable def sortArray_entail_wit_3_1_split_goal_2 : Prop :=
  forall (l : (List Int)) (numsSize_pre : Int) (a_2 : (List Int)) (j_2 : Int) (i_2 : Int) (PreH1 : ((Zlength ((replace_Znth (j_2) ((Znth i_2 a_2 (0 : Int))) ((replace_Znth (i_2) ((Znth j_2 a_2 (0 : Int))) (a_2)))))) = numsSize_pre)) (PreH2 : ((Znth j_2 a_2 (0 : Int)) < (Znth i_2 a_2 (0 : Int)))) (PreH3 : (j_2 < numsSize_pre)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 50000)) (PreH6 : ((0 : Int) <= i_2)) (PreH7 : (i_2 < numsSize_pre)) (PreH8 : ((i_2 + 1) <= j_2)) (PreH9 : (j_2 <= numsSize_pre)) (PreH10 : (Permutation l a_2)) (PreH11 : (increasing (sublist ((0 : Int)) (i_2) (a_2)))) (PreH12 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i_2)) ∧ (i_2 <= q)) ∧ (q < numsSize_pre)) -> ((Znth p a_2 (0 : Int)) <= (Znth q a_2 (0 : Int))))) (PreH13 : (selection_minimum (sublist (i_2) (j_2) (a_2)) (Znth i_2 a_2 (0 : Int)))) ,
  (increasing (sublist ((0 : Int)) (i_2) ((replace_Znth (j_2) ((Znth i_2 a_2 (0 : Int))) ((replace_Znth (i_2) ((Znth j_2 a_2 (0 : Int))) (a_2)))))))

noncomputable def sortArray_entail_wit_3_1_split_goal_3 : Prop :=
  forall (l : (List Int)) (numsSize_pre : Int) (a_2 : (List Int)) (j_2 : Int) (i_2 : Int) (PreH1 : ((Zlength ((replace_Znth (j_2) ((Znth i_2 a_2 (0 : Int))) ((replace_Znth (i_2) ((Znth j_2 a_2 (0 : Int))) (a_2)))))) = numsSize_pre)) (PreH2 : ((Znth j_2 a_2 (0 : Int)) < (Znth i_2 a_2 (0 : Int)))) (PreH3 : (j_2 < numsSize_pre)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 50000)) (PreH6 : ((0 : Int) <= i_2)) (PreH7 : (i_2 < numsSize_pre)) (PreH8 : ((i_2 + 1) <= j_2)) (PreH9 : (j_2 <= numsSize_pre)) (PreH10 : (Permutation l a_2)) (PreH11 : (increasing (sublist ((0 : Int)) (i_2) (a_2)))) (PreH12 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i_2)) ∧ (i_2 <= q)) ∧ (q < numsSize_pre)) -> ((Znth p a_2 (0 : Int)) <= (Znth q a_2 (0 : Int))))) (PreH13 : (selection_minimum (sublist (i_2) (j_2) (a_2)) (Znth i_2 a_2 (0 : Int)))) ,
  (Permutation l (replace_Znth (j_2) ((Znth i_2 a_2 (0 : Int))) ((replace_Znth (i_2) ((Znth j_2 a_2 (0 : Int))) (a_2)))))

noncomputable def sortArray_entail_wit_3_2 : Prop :=
  (
forall (l : (List Int)) (nums_pre : Int) (numsSize_pre : Int) (a_2 : (List Int)) (j_2 : Int) (i_2 : Int) (PreH1 : ((Znth j_2 a_2 (0 : Int)) >= (Znth i_2 a_2 (0 : Int)))) (PreH2 : (j_2 < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : ((0 : Int) <= i_2)) (PreH6 : (i_2 < numsSize_pre)) (PreH7 : ((i_2 + 1) <= j_2)) (PreH8 : (j_2 <= numsSize_pre)) (PreH9 : (Permutation l a_2)) (PreH10 : (increasing (sublist ((0 : Int)) (i_2) (a_2)))) (PreH11 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i_2)) ∧ (i_2 <= q)) ∧ (q < numsSize_pre)) -> ((Znth p a_2 (0 : Int)) <= (Znth q a_2 (0 : Int))))) (PreH12 : (selection_minimum (sublist (i_2) (j_2) (a_2)) (Znth i_2 a_2 (0 : Int)))) ,
  (intArray.full nums_pre numsSize_pre a_2)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i_2))
  ** ((( &( "j" ) )) # Int |-> ((j_2 + 1)))
|--
  EX a : (List Int), EX j : Int, EX i : Int,
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < numsSize_pre) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= numsSize_pre) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((0 : Int)) (i) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < numsSize_pre)) -> ((Znth p a (0 : Int)) <= (Znth q a (0 : Int)))) ” &&
  “ (selection_minimum (sublist (i) (j) (a)) (Znth i a (0 : Int))) ”
  &&  ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full nums_pre numsSize_pre a)
) \/
(
forall (l : (List Int)) (numsSize_pre : Int) (a_2 : (List Int)) (j_2 : Int) (i_2 : Int) (PreH1 : ((Zlength (a_2)) = numsSize_pre)) (PreH2 : ((Znth j_2 a_2 (0 : Int)) >= (Znth i_2 a_2 (0 : Int)))) (PreH3 : (j_2 < numsSize_pre)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 50000)) (PreH6 : ((0 : Int) <= i_2)) (PreH7 : (i_2 < numsSize_pre)) (PreH8 : ((i_2 + 1) <= j_2)) (PreH9 : (j_2 <= numsSize_pre)) (PreH10 : (Permutation l a_2)) (PreH11 : (increasing (sublist ((0 : Int)) (i_2) (a_2)))) (PreH12 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i_2)) ∧ (i_2 <= q)) ∧ (q < numsSize_pre)) -> ((Znth p a_2 (0 : Int)) <= (Znth q a_2 (0 : Int))))) (PreH13 : (selection_minimum (sublist (i_2) (j_2) (a_2)) (Znth i_2 a_2 (0 : Int)))) ,
  TT && emp 
|--
  “ (selection_minimum (sublist (i_2) ((j_2 + 1)) (a_2)) (Znth i_2 a_2 (0 : Int))) ”
  &&  emp
)

noncomputable def sortArray_entail_wit_3_2_split_goal_1 : Prop :=
  forall (l : (List Int)) (numsSize_pre : Int) (a_2 : (List Int)) (j_2 : Int) (i_2 : Int) (PreH1 : ((Zlength (a_2)) = numsSize_pre)) (PreH2 : ((Znth j_2 a_2 (0 : Int)) >= (Znth i_2 a_2 (0 : Int)))) (PreH3 : (j_2 < numsSize_pre)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 50000)) (PreH6 : ((0 : Int) <= i_2)) (PreH7 : (i_2 < numsSize_pre)) (PreH8 : ((i_2 + 1) <= j_2)) (PreH9 : (j_2 <= numsSize_pre)) (PreH10 : (Permutation l a_2)) (PreH11 : (increasing (sublist ((0 : Int)) (i_2) (a_2)))) (PreH12 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i_2)) ∧ (i_2 <= q)) ∧ (q < numsSize_pre)) -> ((Znth p a_2 (0 : Int)) <= (Znth q a_2 (0 : Int))))) (PreH13 : (selection_minimum (sublist (i_2) (j_2) (a_2)) (Znth i_2 a_2 (0 : Int)))) ,
  (selection_minimum (sublist (i_2) ((j_2 + 1)) (a_2)) (Znth i_2 a_2 (0 : Int)))

noncomputable def sortArray_entail_wit_4 : Prop :=
  (
forall (l : (List Int)) (nums_pre : Int) (numsSize_pre : Int) (a_2 : (List Int)) (j : Int) (i_2 : Int) (PreH1 : (j >= numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : ((0 : Int) <= i_2)) (PreH5 : (i_2 < numsSize_pre)) (PreH6 : ((i_2 + 1) <= j)) (PreH7 : (j <= numsSize_pre)) (PreH8 : (Permutation l a_2)) (PreH9 : (increasing (sublist ((0 : Int)) (i_2) (a_2)))) (PreH10 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < i_2)) ∧ (i_2 <= q_2)) ∧ (q_2 < numsSize_pre)) -> ((Znth p_2 a_2 (0 : Int)) <= (Znth q_2 a_2 (0 : Int))))) (PreH11 : (selection_minimum (sublist (i_2) (j) (a_2)) (Znth i_2 a_2 (0 : Int)))) ,
  ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "i" ) )) # Int |-> ((i_2 + 1)))
  ** (intArray.full nums_pre numsSize_pre a_2)
|--
  EX a : (List Int), EX i : Int,
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= numsSize_pre) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((0 : Int)) (i) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < numsSize_pre)) -> ((Znth p a (0 : Int)) <= (Znth q a (0 : Int)))) ”
  &&  ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "numsSize" ) )) # Int |-> (numsSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full nums_pre numsSize_pre a)
) \/
(
forall (l : (List Int)) (numsSize_pre : Int) (a_2 : (List Int)) (j : Int) (i_2 : Int) (PreH1 : ((Zlength (a_2)) = numsSize_pre)) (PreH2 : (j >= numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : ((0 : Int) <= i_2)) (PreH6 : (i_2 < numsSize_pre)) (PreH7 : ((i_2 + 1) <= j)) (PreH8 : (j <= numsSize_pre)) (PreH9 : (Permutation l a_2)) (PreH10 : (increasing (sublist ((0 : Int)) (i_2) (a_2)))) (PreH11 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < i_2)) ∧ (i_2 <= q_2)) ∧ (q_2 < numsSize_pre)) -> ((Znth p_2 a_2 (0 : Int)) <= (Znth q_2 a_2 (0 : Int))))) (PreH12 : (selection_minimum (sublist (i_2) (j) (a_2)) (Znth i_2 a_2 (0 : Int)))) ,
  TT && emp 
|--
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (i_2 + 1))) ∧ ((i_2 + 1) <= q)) ∧ (q < numsSize_pre)) -> ((Znth p a_2 (0 : Int)) <= (Znth q a_2 (0 : Int)))) ” &&
  “ (increasing (sublist ((0 : Int)) ((i_2 + 1)) (a_2))) ”
  &&  emp
)

noncomputable def sortArray_entail_wit_4_split_goal_1 : Prop :=
  forall (l : (List Int)) (numsSize_pre : Int) (a_2 : (List Int)) (j : Int) (i_2 : Int) (PreH1 : ((Zlength (a_2)) = numsSize_pre)) (PreH2 : (j >= numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : ((0 : Int) <= i_2)) (PreH6 : (i_2 < numsSize_pre)) (PreH7 : ((i_2 + 1) <= j)) (PreH8 : (j <= numsSize_pre)) (PreH9 : (Permutation l a_2)) (PreH10 : (increasing (sublist ((0 : Int)) (i_2) (a_2)))) (PreH11 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < i_2)) ∧ (i_2 <= q_2)) ∧ (q_2 < numsSize_pre)) -> ((Znth p_2 a_2 (0 : Int)) <= (Znth q_2 a_2 (0 : Int))))) (PreH12 : (selection_minimum (sublist (i_2) (j) (a_2)) (Znth i_2 a_2 (0 : Int)))) ,
  forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < (i_2 + 1))) ∧ ((i_2 + 1) <= q)) ∧ (q < numsSize_pre)) -> ((Znth p a_2 (0 : Int)) <= (Znth q a_2 (0 : Int))))

noncomputable def sortArray_entail_wit_4_split_goal_2 : Prop :=
  forall (l : (List Int)) (numsSize_pre : Int) (a_2 : (List Int)) (j : Int) (i_2 : Int) (PreH1 : ((Zlength (a_2)) = numsSize_pre)) (PreH2 : (j >= numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : ((0 : Int) <= i_2)) (PreH6 : (i_2 < numsSize_pre)) (PreH7 : ((i_2 + 1) <= j)) (PreH8 : (j <= numsSize_pre)) (PreH9 : (Permutation l a_2)) (PreH10 : (increasing (sublist ((0 : Int)) (i_2) (a_2)))) (PreH11 : forall (p_2 : Int) , forall (q_2 : Int) , ((((((0 : Int) <= p_2) ∧ (p_2 < i_2)) ∧ (i_2 <= q_2)) ∧ (q_2 < numsSize_pre)) -> ((Znth p_2 a_2 (0 : Int)) <= (Znth q_2 a_2 (0 : Int))))) (PreH12 : (selection_minimum (sublist (i_2) (j) (a_2)) (Znth i_2 a_2 (0 : Int)))) ,
  (increasing (sublist ((0 : Int)) ((i_2 + 1)) (a_2)))

noncomputable def sortArray_return_wit_1 : Prop :=
  (
forall (l : (List Int)) (nums_pre : Int) (numsSize_pre : Int) (a : (List Int)) (i : Int) (PreH1 : (i >= numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= numsSize_pre)) (PreH6 : (Permutation l a)) (PreH7 : (increasing (sublist ((0 : Int)) (i) (a)))) (PreH8 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < numsSize_pre)) -> ((Znth p a (0 : Int)) <= (Znth q a (0 : Int))))) ,
  (intArray.full nums_pre numsSize_pre a)
|--
  EX l1 : (List Int),
  “ (Permutation l l1) ” &&
  “ (increasing l1) ”
  &&  (intArray.full nums_pre numsSize_pre l1)
) \/
(
forall (l : (List Int)) (numsSize_pre : Int) (a : (List Int)) (i : Int) (PreH1 : ((Zlength (a)) = numsSize_pre)) (PreH2 : (i >= numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (Permutation l a)) (PreH8 : (increasing (sublist ((0 : Int)) (i) (a)))) (PreH9 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < numsSize_pre)) -> ((Znth p a (0 : Int)) <= (Znth q a (0 : Int))))) ,
  TT && emp 
|--
  “ (increasing a) ”
  &&  emp
)

noncomputable def sortArray_return_wit_1_split_goal_1 : Prop :=
  forall (l : (List Int)) (numsSize_pre : Int) (a : (List Int)) (i : Int) (PreH1 : ((Zlength (a)) = numsSize_pre)) (PreH2 : (i >= numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (Permutation l a)) (PreH8 : (increasing (sublist ((0 : Int)) (i) (a)))) (PreH9 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < numsSize_pre)) -> ((Znth p a (0 : Int)) <= (Znth q a (0 : Int))))) ,
  (increasing a)

noncomputable def sortArray_partial_solve_wit_1 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (numsSize_pre : Int) (a : (List Int)) (j : Int) (i : Int) (PreH1 : (j < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < numsSize_pre)) (PreH6 : ((i + 1) <= j)) (PreH7 : (j <= numsSize_pre)) (PreH8 : (Permutation l a)) (PreH9 : (increasing (sublist ((0 : Int)) (i) (a)))) (PreH10 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < numsSize_pre)) -> ((Znth p a (0 : Int)) <= (Znth q a (0 : Int))))) (PreH11 : (selection_minimum (sublist (i) (j) (a)) (Znth i a (0 : Int)))) ,
  (intArray.full nums_pre numsSize_pre a)
|--
  “ (j < numsSize_pre) ” &&
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < numsSize_pre) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= numsSize_pre) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((0 : Int)) (i) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < numsSize_pre)) -> ((Znth p a (0 : Int)) <= (Znth q a (0 : Int)))) ” &&
  “ (selection_minimum (sublist (i) (j) (a)) (Znth i a (0 : Int))) ”
  &&  (((nums_pre + (j * sizeof(INT)))) # Int |-> ((Znth j a (0 : Int))))
  ** (intArray.missing_i nums_pre j (0 : Int) numsSize_pre a)

noncomputable def sortArray_partial_solve_wit_2 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (numsSize_pre : Int) (a : (List Int)) (j : Int) (i : Int) (PreH1 : (j < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < numsSize_pre)) (PreH6 : ((i + 1) <= j)) (PreH7 : (j <= numsSize_pre)) (PreH8 : (Permutation l a)) (PreH9 : (increasing (sublist ((0 : Int)) (i) (a)))) (PreH10 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < numsSize_pre)) -> ((Znth p a (0 : Int)) <= (Znth q a (0 : Int))))) (PreH11 : (selection_minimum (sublist (i) (j) (a)) (Znth i a (0 : Int)))) ,
  (intArray.full nums_pre numsSize_pre a)
|--
  “ (j < numsSize_pre) ” &&
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < numsSize_pre) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= numsSize_pre) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((0 : Int)) (i) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < numsSize_pre)) -> ((Znth p a (0 : Int)) <= (Znth q a (0 : Int)))) ” &&
  “ (selection_minimum (sublist (i) (j) (a)) (Znth i a (0 : Int))) ”
  &&  (((nums_pre + (i * sizeof(INT)))) # Int |-> ((Znth i a (0 : Int))))
  ** (intArray.missing_i nums_pre i (0 : Int) numsSize_pre a)

noncomputable def sortArray_partial_solve_wit_3 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (numsSize_pre : Int) (a : (List Int)) (j : Int) (i : Int) (PreH1 : ((Znth j a (0 : Int)) < (Znth i a (0 : Int)))) (PreH2 : (j < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : ((i + 1) <= j)) (PreH8 : (j <= numsSize_pre)) (PreH9 : (Permutation l a)) (PreH10 : (increasing (sublist ((0 : Int)) (i) (a)))) (PreH11 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < numsSize_pre)) -> ((Znth p a (0 : Int)) <= (Znth q a (0 : Int))))) (PreH12 : (selection_minimum (sublist (i) (j) (a)) (Znth i a (0 : Int)))) ,
  (intArray.full nums_pre numsSize_pre a)
|--
  “ ((Znth j a (0 : Int)) < (Znth i a (0 : Int))) ” &&
  “ (j < numsSize_pre) ” &&
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < numsSize_pre) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= numsSize_pre) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((0 : Int)) (i) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < numsSize_pre)) -> ((Znth p a (0 : Int)) <= (Znth q a (0 : Int)))) ” &&
  “ (selection_minimum (sublist (i) (j) (a)) (Znth i a (0 : Int))) ”
  &&  (((nums_pre + (i * sizeof(INT)))) # Int |-> ((Znth i a (0 : Int))))
  ** (intArray.missing_i nums_pre i (0 : Int) numsSize_pre a)

noncomputable def sortArray_partial_solve_wit_4 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (numsSize_pre : Int) (a : (List Int)) (j : Int) (i : Int) (PreH1 : ((Znth j a (0 : Int)) < (Znth i a (0 : Int)))) (PreH2 : (j < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : ((i + 1) <= j)) (PreH8 : (j <= numsSize_pre)) (PreH9 : (Permutation l a)) (PreH10 : (increasing (sublist ((0 : Int)) (i) (a)))) (PreH11 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < numsSize_pre)) -> ((Znth p a (0 : Int)) <= (Znth q a (0 : Int))))) (PreH12 : (selection_minimum (sublist (i) (j) (a)) (Znth i a (0 : Int)))) ,
  (intArray.full nums_pre numsSize_pre a)
|--
  “ ((Znth j a (0 : Int)) < (Znth i a (0 : Int))) ” &&
  “ (j < numsSize_pre) ” &&
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < numsSize_pre) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= numsSize_pre) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((0 : Int)) (i) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < numsSize_pre)) -> ((Znth p a (0 : Int)) <= (Znth q a (0 : Int)))) ” &&
  “ (selection_minimum (sublist (i) (j) (a)) (Znth i a (0 : Int))) ”
  &&  (((nums_pre + (j * sizeof(INT)))) # Int |-> ((Znth j a (0 : Int))))
  ** (intArray.missing_i nums_pre j (0 : Int) numsSize_pre a)

noncomputable def sortArray_partial_solve_wit_5 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (numsSize_pre : Int) (a : (List Int)) (j : Int) (i : Int) (PreH1 : ((Znth j a (0 : Int)) < (Znth i a (0 : Int)))) (PreH2 : (j < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : ((i + 1) <= j)) (PreH8 : (j <= numsSize_pre)) (PreH9 : (Permutation l a)) (PreH10 : (increasing (sublist ((0 : Int)) (i) (a)))) (PreH11 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < numsSize_pre)) -> ((Znth p a (0 : Int)) <= (Znth q a (0 : Int))))) (PreH12 : (selection_minimum (sublist (i) (j) (a)) (Znth i a (0 : Int)))) ,
  (intArray.full nums_pre numsSize_pre a)
|--
  “ ((Znth j a (0 : Int)) < (Znth i a (0 : Int))) ” &&
  “ (j < numsSize_pre) ” &&
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < numsSize_pre) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= numsSize_pre) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((0 : Int)) (i) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < numsSize_pre)) -> ((Znth p a (0 : Int)) <= (Znth q a (0 : Int)))) ” &&
  “ (selection_minimum (sublist (i) (j) (a)) (Znth i a (0 : Int))) ”
  &&  (((nums_pre + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i nums_pre i (0 : Int) numsSize_pre a)

noncomputable def sortArray_partial_solve_wit_6 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (numsSize_pre : Int) (a : (List Int)) (j : Int) (i : Int) (PreH1 : ((Znth j a (0 : Int)) < (Znth i a (0 : Int)))) (PreH2 : (j < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : ((i + 1) <= j)) (PreH8 : (j <= numsSize_pre)) (PreH9 : (Permutation l a)) (PreH10 : (increasing (sublist ((0 : Int)) (i) (a)))) (PreH11 : forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < numsSize_pre)) -> ((Znth p a (0 : Int)) <= (Znth q a (0 : Int))))) (PreH12 : (selection_minimum (sublist (i) (j) (a)) (Znth i a (0 : Int)))) ,
  (intArray.full nums_pre numsSize_pre (replace_Znth (i) ((Znth j a (0 : Int))) (a)))
|--
  “ ((Znth j a (0 : Int)) < (Znth i a (0 : Int))) ” &&
  “ (j < numsSize_pre) ” &&
  “ (1 <= numsSize_pre) ” &&
  “ (numsSize_pre <= 50000) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < numsSize_pre) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= numsSize_pre) ” &&
  “ (Permutation l a) ” &&
  “ (increasing (sublist ((0 : Int)) (i) (a))) ” &&
  “ forall (p : Int) , forall (q : Int) , ((((((0 : Int) <= p) ∧ (p < i)) ∧ (i <= q)) ∧ (q < numsSize_pre)) -> ((Znth p a (0 : Int)) <= (Znth q a (0 : Int)))) ” &&
  “ (selection_minimum (sublist (i) (j) (a)) (Znth i a (0 : Int))) ”
  &&  (((nums_pre + (j * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i nums_pre j (0 : Int) numsSize_pre (replace_Znth (i) ((Znth j a (0 : Int))) (a)))


structure VC_Correct : Type where
  proof_of_sortArray_safety_wit_1 : sortArray_safety_wit_1
  proof_of_sortArray_safety_wit_2 : sortArray_safety_wit_2
  proof_of_sortArray_safety_wit_3 : sortArray_safety_wit_3
  proof_of_sortArray_safety_wit_4 : sortArray_safety_wit_4
  proof_of_sortArray_safety_wit_5 : sortArray_safety_wit_5
  proof_of_sortArray_safety_wit_6 : sortArray_safety_wit_6
  proof_of_sortArray_partial_solve_wit_1 : sortArray_partial_solve_wit_1
  proof_of_sortArray_partial_solve_wit_2 : sortArray_partial_solve_wit_2
  proof_of_sortArray_partial_solve_wit_3 : sortArray_partial_solve_wit_3
  proof_of_sortArray_partial_solve_wit_4 : sortArray_partial_solve_wit_4
  proof_of_sortArray_partial_solve_wit_5 : sortArray_partial_solve_wit_5
  proof_of_sortArray_partial_solve_wit_6 : sortArray_partial_solve_wit_6
  proof_of_sortArray_entail_wit_1 : sortArray_entail_wit_1
  proof_of_sortArray_entail_wit_2 : sortArray_entail_wit_2
  proof_of_sortArray_entail_wit_3_1 : sortArray_entail_wit_3_1
  proof_of_sortArray_entail_wit_3_2 : sortArray_entail_wit_3_2
  proof_of_sortArray_entail_wit_4 : sortArray_entail_wit_4
  proof_of_sortArray_return_wit_1 : sortArray_return_wit_1

end SimpleC.EE.LLM_bench.Algorithms.selection_sort.selection_sort_goal
