import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P014_1784A_monsters_easy_version_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def solver_safety_wit_1 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (sorted : (List Int)) (PreH1 : (Permutation input sorted)) (PreH2 : (increasing sorted)) (PreH3 : ((Zlength (sorted)) = n_pre)) (PreH4 : (FullPreparationSpecBridge input sorted)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (1 <= (Zlength (input)))) (PreH7 : ((Zlength (input)) <= 200000)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (input)))) -> ((1 <= (Znth i input (0 : Int))) ∧ ((Znth i input (0 : Int)) <= (Zlength (input)))))) ,
  ((( &( "spent" ) )) # Int64 |->_)
  ** (intArray.full a_pre n_pre sorted)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (sorted : (List Int)) (PreH1 : (Permutation input sorted)) (PreH2 : (increasing sorted)) (PreH3 : ((Zlength (sorted)) = n_pre)) (PreH4 : (FullPreparationSpecBridge input sorted)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (1 <= (Zlength (input)))) (PreH7 : ((Zlength (input)) <= 200000)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (input)))) -> ((1 <= (Znth i input (0 : Int))) ∧ ((Znth i input (0 : Int)) <= (Zlength (input)))))) ,
  ((( &( "kept" ) )) # Int |->_)
  ** ((( &( "spent" ) )) # Int64 |-> ((0 : Int)))
  ** (intArray.full a_pre n_pre sorted)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (sorted : (List Int)) (PreH1 : (Permutation input sorted)) (PreH2 : (increasing sorted)) (PreH3 : ((Zlength (sorted)) = n_pre)) (PreH4 : (FullPreparationSpecBridge input sorted)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (1 <= (Zlength (input)))) (PreH7 : ((Zlength (input)) <= 200000)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (input)))) -> ((1 <= (Znth i input (0 : Int))) ∧ ((Znth i input (0 : Int)) <= (Zlength (input)))))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "kept" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "spent" ) )) # Int64 |-> ((0 : Int)))
  ** (intArray.full a_pre n_pre sorted)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (spent : Int) (kept : Int) (i : Int) (sorted : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (Permutation input sorted)) (PreH7 : (increasing sorted)) (PreH8 : (FullPreparationSpecBridge input sorted)) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k sorted (0 : Int))) ∧ ((Znth k sorted (0 : Int)) <= n_pre)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= kept)) (PreH13 : (kept <= i)) (PreH14 : ((0 : Int) <= spent)) (PreH15 : (spent <= (i * n_pre))) (PreH16 : (PrefixGreedyState input sorted i kept spent)) ,
  ((( &( "next" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "kept" ) )) # Int |-> (kept))
  ** ((( &( "spent" ) )) # Int64 |-> (spent))
  ** (intArray.full a_pre n_pre sorted)
|--
  “ ((kept + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (kept + 1)) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (spent : Int) (kept : Int) (i : Int) (sorted : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (Permutation input sorted)) (PreH7 : (increasing sorted)) (PreH8 : (FullPreparationSpecBridge input sorted)) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k sorted (0 : Int))) ∧ ((Znth k sorted (0 : Int)) <= n_pre)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= kept)) (PreH13 : (kept <= i)) (PreH14 : ((0 : Int) <= spent)) (PreH15 : (spent <= (i * n_pre))) (PreH16 : (PrefixGreedyState input sorted i kept spent)) ,
  ((( &( "next" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "kept" ) )) # Int |-> (kept))
  ** ((( &( "spent" ) )) # Int64 |-> (spent))
  ** (intArray.full a_pre n_pre sorted)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (spent : Int) (kept : Int) (i : Int) (sorted : (List Int)) (PreH1 : ((kept + 1) > (Znth i sorted (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (Permutation input sorted)) (PreH8 : (increasing sorted)) (PreH9 : (FullPreparationSpecBridge input sorted)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k sorted (0 : Int))) ∧ ((Znth k sorted (0 : Int)) <= n_pre)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= kept)) (PreH14 : (kept <= i)) (PreH15 : ((0 : Int) <= spent)) (PreH16 : (spent <= (i * n_pre))) (PreH17 : (PrefixGreedyState input sorted i kept spent)) ,
  (intArray.full a_pre n_pre sorted)
  ** ((( &( "next" ) )) # Int |-> ((Znth i sorted (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "kept" ) )) # Int |-> (kept))
  ** ((( &( "spent" ) )) # Int64 |-> (spent))
|--
  “ ((spent + ((Znth i sorted (0 : Int)) - (Znth i sorted (0 : Int)))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (spent + ((Znth i sorted (0 : Int)) - (Znth i sorted (0 : Int))))) ”

noncomputable def solver_safety_wit_7 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (spent : Int) (kept : Int) (i : Int) (sorted : (List Int)) (PreH1 : ((kept + 1) > (Znth i sorted (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (Permutation input sorted)) (PreH8 : (increasing sorted)) (PreH9 : (FullPreparationSpecBridge input sorted)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k sorted (0 : Int))) ∧ ((Znth k sorted (0 : Int)) <= n_pre)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= kept)) (PreH14 : (kept <= i)) (PreH15 : ((0 : Int) <= spent)) (PreH16 : (spent <= (i * n_pre))) (PreH17 : (PrefixGreedyState input sorted i kept spent)) ,
  (intArray.full a_pre n_pre sorted)
  ** ((( &( "next" ) )) # Int |-> ((Znth i sorted (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "kept" ) )) # Int |-> (kept))
  ** ((( &( "spent" ) )) # Int64 |-> (spent))
|--
  “ (((Znth i sorted (0 : Int)) - (Znth i sorted (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth i sorted (0 : Int)) - (Znth i sorted (0 : Int)))) ”

noncomputable def solver_safety_wit_8 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (spent : Int) (kept : Int) (i : Int) (sorted : (List Int)) (PreH1 : ((kept + 1) <= (Znth i sorted (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (Permutation input sorted)) (PreH8 : (increasing sorted)) (PreH9 : (FullPreparationSpecBridge input sorted)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k sorted (0 : Int))) ∧ ((Znth k sorted (0 : Int)) <= n_pre)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= kept)) (PreH14 : (kept <= i)) (PreH15 : ((0 : Int) <= spent)) (PreH16 : (spent <= (i * n_pre))) (PreH17 : (PrefixGreedyState input sorted i kept spent)) ,
  (intArray.full a_pre n_pre sorted)
  ** ((( &( "next" ) )) # Int |-> ((kept + 1)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "kept" ) )) # Int |-> (kept))
  ** ((( &( "spent" ) )) # Int64 |-> (spent))
|--
  “ ((spent + ((Znth i sorted (0 : Int)) - (kept + 1))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (spent + ((Znth i sorted (0 : Int)) - (kept + 1)))) ”

noncomputable def solver_safety_wit_9 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (spent : Int) (kept : Int) (i : Int) (sorted : (List Int)) (PreH1 : ((kept + 1) <= (Znth i sorted (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (Permutation input sorted)) (PreH8 : (increasing sorted)) (PreH9 : (FullPreparationSpecBridge input sorted)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k sorted (0 : Int))) ∧ ((Znth k sorted (0 : Int)) <= n_pre)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= kept)) (PreH14 : (kept <= i)) (PreH15 : ((0 : Int) <= spent)) (PreH16 : (spent <= (i * n_pre))) (PreH17 : (PrefixGreedyState input sorted i kept spent)) ,
  (intArray.full a_pre n_pre sorted)
  ** ((( &( "next" ) )) # Int |-> ((kept + 1)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "kept" ) )) # Int |-> (kept))
  ** ((( &( "spent" ) )) # Int64 |-> (spent))
|--
  “ (((Znth i sorted (0 : Int)) - (kept + 1)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth i sorted (0 : Int)) - (kept + 1))) ”

noncomputable def solver_safety_wit_10 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (spent : Int) (kept : Int) (i : Int) (sorted : (List Int)) (PreH1 : ((kept + 1) > (Znth i sorted (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (Permutation input sorted)) (PreH8 : (increasing sorted)) (PreH9 : (FullPreparationSpecBridge input sorted)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k sorted (0 : Int))) ∧ ((Znth k sorted (0 : Int)) <= n_pre)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= kept)) (PreH14 : (kept <= i)) (PreH15 : ((0 : Int) <= spent)) (PreH16 : (spent <= (i * n_pre))) (PreH17 : (PrefixGreedyState input sorted i kept spent)) ,
  (intArray.full a_pre n_pre sorted)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "kept" ) )) # Int |-> ((Znth i sorted (0 : Int))))
  ** ((( &( "spent" ) )) # Int64 |-> ((spent + ((Znth i sorted (0 : Int)) - (Znth i sorted (0 : Int))))))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_11 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (spent : Int) (kept : Int) (i : Int) (sorted : (List Int)) (PreH1 : ((kept + 1) <= (Znth i sorted (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (Permutation input sorted)) (PreH8 : (increasing sorted)) (PreH9 : (FullPreparationSpecBridge input sorted)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k sorted (0 : Int))) ∧ ((Znth k sorted (0 : Int)) <= n_pre)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= kept)) (PreH14 : (kept <= i)) (PreH15 : ((0 : Int) <= spent)) (PreH16 : (spent <= (i * n_pre))) (PreH17 : (PrefixGreedyState input sorted i kept spent)) ,
  (intArray.full a_pre n_pre sorted)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "kept" ) )) # Int |-> ((kept + 1)))
  ** ((( &( "spent" ) )) # Int64 |-> ((spent + ((Znth i sorted (0 : Int)) - (kept + 1)))))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (sorted_2 : (List Int)) (PreH1 : (Permutation input sorted_2)) (PreH2 : (increasing sorted_2)) (PreH3 : ((Zlength (sorted_2)) = n_pre)) (PreH4 : (FullPreparationSpecBridge input sorted_2)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (1 <= (Zlength (input)))) (PreH7 : ((Zlength (input)) <= 200000)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (input)))) -> ((1 <= (Znth i input (0 : Int))) ∧ ((Znth i input (0 : Int)) <= (Zlength (input)))))) ,
  (intArray.full a_pre n_pre sorted_2)
|--
  EX sorted : (List Int),
  “ (n_pre = (Zlength (input))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((Zlength (sorted)) = n_pre) ” &&
  “ (Permutation input sorted) ” &&
  “ (increasing sorted) ” &&
  “ (FullPreparationSpecBridge input sorted) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k sorted (0 : Int))) ∧ ((Znth k sorted (0 : Int)) <= n_pre))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= ((0 : Int) * n_pre)) ” &&
  “ (PrefixGreedyState input sorted (0 : Int) (0 : Int) (0 : Int)) ”
  &&  (intArray.full a_pre n_pre sorted)
) \/
(
forall (n_pre : Int) (input : (List Int)) (sorted_2 : (List Int)) (PreH1 : (Permutation input sorted_2)) (PreH2 : (increasing sorted_2)) (PreH3 : ((Zlength (sorted_2)) = n_pre)) (PreH4 : (FullPreparationSpecBridge input sorted_2)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (1 <= (Zlength (input)))) (PreH7 : ((Zlength (input)) <= 200000)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (input)))) -> ((1 <= (Znth i input (0 : Int))) ∧ ((Znth i input (0 : Int)) <= (Zlength (input)))))) ,
  TT && emp 
|--
  “ (PrefixGreedyState input sorted_2 (0 : Int) (0 : Int) (0 : Int)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k sorted_2 (0 : Int))) ∧ ((Znth k sorted_2 (0 : Int)) <= n_pre))) ”
  &&  emp
)

noncomputable def solver_entail_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (sorted_2 : (List Int)) (PreH1 : (Permutation input sorted_2)) (PreH2 : (increasing sorted_2)) (PreH3 : ((Zlength (sorted_2)) = n_pre)) (PreH4 : (FullPreparationSpecBridge input sorted_2)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (1 <= (Zlength (input)))) (PreH7 : ((Zlength (input)) <= 200000)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (input)))) -> ((1 <= (Znth i input (0 : Int))) ∧ ((Znth i input (0 : Int)) <= (Zlength (input)))))) ,
  (PrefixGreedyState input sorted_2 (0 : Int) (0 : Int) (0 : Int))

noncomputable def solver_entail_wit_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (sorted_2 : (List Int)) (PreH1 : (Permutation input sorted_2)) (PreH2 : (increasing sorted_2)) (PreH3 : ((Zlength (sorted_2)) = n_pre)) (PreH4 : (FullPreparationSpecBridge input sorted_2)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (1 <= (Zlength (input)))) (PreH7 : ((Zlength (input)) <= 200000)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (input)))) -> ((1 <= (Znth i input (0 : Int))) ∧ ((Znth i input (0 : Int)) <= (Zlength (input)))))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k sorted_2 (0 : Int))) ∧ ((Znth k sorted_2 (0 : Int)) <= n_pre)))

noncomputable def solver_entail_wit_2_1 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (spent : Int) (kept : Int) (i : Int) (sorted_2 : (List Int)) (PreH1 : ((kept + 1) > (Znth i sorted_2 (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted_2)) = n_pre)) (PreH7 : (Permutation input sorted_2)) (PreH8 : (increasing sorted_2)) (PreH9 : (FullPreparationSpecBridge input sorted_2)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k sorted_2 (0 : Int))) ∧ ((Znth k sorted_2 (0 : Int)) <= n_pre)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= kept)) (PreH14 : (kept <= i)) (PreH15 : ((0 : Int) <= spent)) (PreH16 : (spent <= (i * n_pre))) (PreH17 : (PrefixGreedyState input sorted_2 i kept spent)) ,
  (intArray.full a_pre n_pre sorted_2)
|--
  EX sorted : (List Int),
  “ (n_pre = (Zlength (input))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((Zlength (sorted)) = n_pre) ” &&
  “ (Permutation input sorted) ” &&
  “ (increasing sorted) ” &&
  “ (FullPreparationSpecBridge input sorted) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k sorted (0 : Int))) ∧ ((Znth k sorted (0 : Int)) <= n_pre))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= (Znth i sorted_2 (0 : Int))) ” &&
  “ ((Znth i sorted_2 (0 : Int)) <= (i + 1)) ” &&
  “ ((0 : Int) <= (spent + ((Znth i sorted_2 (0 : Int)) - (Znth i sorted_2 (0 : Int))))) ” &&
  “ ((spent + ((Znth i sorted_2 (0 : Int)) - (Znth i sorted_2 (0 : Int)))) <= ((i + 1) * n_pre)) ” &&
  “ (PrefixGreedyState input sorted (i + 1) (Znth i sorted_2 (0 : Int)) (spent + ((Znth i sorted_2 (0 : Int)) - (Znth i sorted_2 (0 : Int))))) ”
  &&  (intArray.full a_pre n_pre sorted)
) \/
(
forall (n_pre : Int) (input : (List Int)) (spent : Int) (kept : Int) (i : Int) (sorted_2 : (List Int)) (PreH1 : ((kept + 1) > (Znth i sorted_2 (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted_2)) = n_pre)) (PreH7 : (Permutation input sorted_2)) (PreH8 : (increasing sorted_2)) (PreH9 : (FullPreparationSpecBridge input sorted_2)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k sorted_2 (0 : Int))) ∧ ((Znth k sorted_2 (0 : Int)) <= n_pre)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= kept)) (PreH14 : (kept <= i)) (PreH15 : ((0 : Int) <= spent)) (PreH16 : (spent <= (i * n_pre))) (PreH17 : (PrefixGreedyState input sorted_2 i kept spent)) ,
  TT && emp 
|--
  “ (PrefixGreedyState input sorted_2 (i + 1) (Znth i sorted_2 (0 : Int)) (spent + ((Znth i sorted_2 (0 : Int)) - (Znth i sorted_2 (0 : Int))))) ” &&
  “ ((spent + ((Znth i sorted_2 (0 : Int)) - (Znth i sorted_2 (0 : Int)))) <= ((i + 1) * n_pre)) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (spent : Int) (kept : Int) (i : Int) (sorted_2 : (List Int)) (PreH1 : ((kept + 1) > (Znth i sorted_2 (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted_2)) = n_pre)) (PreH7 : (Permutation input sorted_2)) (PreH8 : (increasing sorted_2)) (PreH9 : (FullPreparationSpecBridge input sorted_2)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k sorted_2 (0 : Int))) ∧ ((Znth k sorted_2 (0 : Int)) <= n_pre)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= kept)) (PreH14 : (kept <= i)) (PreH15 : ((0 : Int) <= spent)) (PreH16 : (spent <= (i * n_pre))) (PreH17 : (PrefixGreedyState input sorted_2 i kept spent)) ,
  (PrefixGreedyState input sorted_2 (i + 1) (Znth i sorted_2 (0 : Int)) (spent + ((Znth i sorted_2 (0 : Int)) - (Znth i sorted_2 (0 : Int)))))

noncomputable def solver_entail_wit_2_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (spent : Int) (kept : Int) (i : Int) (sorted_2 : (List Int)) (PreH1 : ((kept + 1) > (Znth i sorted_2 (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted_2)) = n_pre)) (PreH7 : (Permutation input sorted_2)) (PreH8 : (increasing sorted_2)) (PreH9 : (FullPreparationSpecBridge input sorted_2)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k sorted_2 (0 : Int))) ∧ ((Znth k sorted_2 (0 : Int)) <= n_pre)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= kept)) (PreH14 : (kept <= i)) (PreH15 : ((0 : Int) <= spent)) (PreH16 : (spent <= (i * n_pre))) (PreH17 : (PrefixGreedyState input sorted_2 i kept spent)) ,
  ((spent + ((Znth i sorted_2 (0 : Int)) - (Znth i sorted_2 (0 : Int)))) <= ((i + 1) * n_pre))

noncomputable def solver_entail_wit_2_2 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (spent : Int) (kept : Int) (i : Int) (sorted_2 : (List Int)) (PreH1 : ((kept + 1) <= (Znth i sorted_2 (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted_2)) = n_pre)) (PreH7 : (Permutation input sorted_2)) (PreH8 : (increasing sorted_2)) (PreH9 : (FullPreparationSpecBridge input sorted_2)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k sorted_2 (0 : Int))) ∧ ((Znth k sorted_2 (0 : Int)) <= n_pre)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= kept)) (PreH14 : (kept <= i)) (PreH15 : ((0 : Int) <= spent)) (PreH16 : (spent <= (i * n_pre))) (PreH17 : (PrefixGreedyState input sorted_2 i kept spent)) ,
  (intArray.full a_pre n_pre sorted_2)
|--
  EX sorted : (List Int),
  “ (n_pre = (Zlength (input))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((Zlength (sorted)) = n_pre) ” &&
  “ (Permutation input sorted) ” &&
  “ (increasing sorted) ” &&
  “ (FullPreparationSpecBridge input sorted) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k sorted (0 : Int))) ∧ ((Znth k sorted (0 : Int)) <= n_pre))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= (kept + 1)) ” &&
  “ ((kept + 1) <= (i + 1)) ” &&
  “ ((0 : Int) <= (spent + ((Znth i sorted_2 (0 : Int)) - (kept + 1)))) ” &&
  “ ((spent + ((Znth i sorted_2 (0 : Int)) - (kept + 1))) <= ((i + 1) * n_pre)) ” &&
  “ (PrefixGreedyState input sorted (i + 1) (kept + 1) (spent + ((Znth i sorted_2 (0 : Int)) - (kept + 1)))) ”
  &&  (intArray.full a_pre n_pre sorted)
) \/
(
forall (n_pre : Int) (input : (List Int)) (spent : Int) (kept : Int) (i : Int) (sorted_2 : (List Int)) (PreH1 : ((kept + 1) <= (Znth i sorted_2 (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted_2)) = n_pre)) (PreH7 : (Permutation input sorted_2)) (PreH8 : (increasing sorted_2)) (PreH9 : (FullPreparationSpecBridge input sorted_2)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k sorted_2 (0 : Int))) ∧ ((Znth k sorted_2 (0 : Int)) <= n_pre)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= kept)) (PreH14 : (kept <= i)) (PreH15 : ((0 : Int) <= spent)) (PreH16 : (spent <= (i * n_pre))) (PreH17 : (PrefixGreedyState input sorted_2 i kept spent)) ,
  TT && emp 
|--
  “ (PrefixGreedyState input sorted_2 (i + 1) (kept + 1) (spent + ((Znth i sorted_2 (0 : Int)) - (kept + 1)))) ” &&
  “ ((spent + ((Znth i sorted_2 (0 : Int)) - (kept + 1))) <= ((i + 1) * n_pre)) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (spent : Int) (kept : Int) (i : Int) (sorted_2 : (List Int)) (PreH1 : ((kept + 1) <= (Znth i sorted_2 (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted_2)) = n_pre)) (PreH7 : (Permutation input sorted_2)) (PreH8 : (increasing sorted_2)) (PreH9 : (FullPreparationSpecBridge input sorted_2)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k sorted_2 (0 : Int))) ∧ ((Znth k sorted_2 (0 : Int)) <= n_pre)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= kept)) (PreH14 : (kept <= i)) (PreH15 : ((0 : Int) <= spent)) (PreH16 : (spent <= (i * n_pre))) (PreH17 : (PrefixGreedyState input sorted_2 i kept spent)) ,
  (PrefixGreedyState input sorted_2 (i + 1) (kept + 1) (spent + ((Znth i sorted_2 (0 : Int)) - (kept + 1))))

noncomputable def solver_entail_wit_2_2_split_goal_2 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (spent : Int) (kept : Int) (i : Int) (sorted_2 : (List Int)) (PreH1 : ((kept + 1) <= (Znth i sorted_2 (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted_2)) = n_pre)) (PreH7 : (Permutation input sorted_2)) (PreH8 : (increasing sorted_2)) (PreH9 : (FullPreparationSpecBridge input sorted_2)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k sorted_2 (0 : Int))) ∧ ((Znth k sorted_2 (0 : Int)) <= n_pre)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= kept)) (PreH14 : (kept <= i)) (PreH15 : ((0 : Int) <= spent)) (PreH16 : (spent <= (i * n_pre))) (PreH17 : (PrefixGreedyState input sorted_2 i kept spent)) ,
  ((spent + ((Znth i sorted_2 (0 : Int)) - (kept + 1))) <= ((i + 1) * n_pre))

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (spent : Int) (kept : Int) (i : Int) (sorted : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (Permutation input sorted)) (PreH7 : (increasing sorted)) (PreH8 : (FullPreparationSpecBridge input sorted)) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k sorted (0 : Int))) ∧ ((Znth k sorted (0 : Int)) <= n_pre)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= kept)) (PreH13 : (kept <= i)) (PreH14 : ((0 : Int) <= spent)) (PreH15 : (spent <= (i * n_pre))) (PreH16 : (PrefixGreedyState input sorted i kept spent)) ,
  (intArray.full a_pre n_pre sorted)
|--
  EX post : (List Int),
  “ (Spec input spent) ”
  &&  (intArray.full a_pre n_pre post)
) \/
(
forall (n_pre : Int) (input : (List Int)) (spent : Int) (kept : Int) (i : Int) (sorted : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (Permutation input sorted)) (PreH7 : (increasing sorted)) (PreH8 : (FullPreparationSpecBridge input sorted)) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k sorted (0 : Int))) ∧ ((Znth k sorted (0 : Int)) <= n_pre)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= kept)) (PreH13 : (kept <= i)) (PreH14 : ((0 : Int) <= spent)) (PreH15 : (spent <= (i * n_pre))) (PreH16 : (PrefixGreedyState input sorted i kept spent)) ,
  TT && emp 
|--
  “ (Spec input spent) ”
  &&  emp
)

noncomputable def solver_return_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (spent : Int) (kept : Int) (i : Int) (sorted : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (Permutation input sorted)) (PreH7 : (increasing sorted)) (PreH8 : (FullPreparationSpecBridge input sorted)) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k sorted (0 : Int))) ∧ ((Znth k sorted (0 : Int)) <= n_pre)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= kept)) (PreH13 : (kept <= i)) (PreH14 : ((0 : Int) <= spent)) (PreH15 : (spent <= (i * n_pre))) (PreH16 : (PrefixGreedyState input sorted i kept spent)) ,
  (Spec input spent)

noncomputable def solver_partial_solve_wit_1_pure : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 200000)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (input)))) -> ((1 <= (Znth i input (0 : Int))) ∧ ((Znth i input (0 : Int)) <= (Zlength (input)))))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre input)
|--
  “ (n_pre = (Zlength (input))) ”

noncomputable def solver_partial_solve_wit_1_aux : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 200000)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (input)))) -> ((1 <= (Znth i input (0 : Int))) ∧ ((Znth i input (0 : Int)) <= (Zlength (input)))))) ,
  (intArray.full a_pre n_pre input)
|--
  “ (n_pre = (Zlength (input))) ” &&
  “ (n_pre = (Zlength (input))) ” &&
  “ (1 <= (Zlength (input))) ” &&
  “ ((Zlength (input)) <= 200000) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (input)))) -> ((1 <= (Znth i input (0 : Int))) ∧ ((Znth i input (0 : Int)) <= (Zlength (input))))) ”
  &&  (intArray.full a_pre n_pre input)

noncomputable def solver_partial_solve_wit_1 : Prop := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux

noncomputable def solver_partial_solve_wit_2 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (spent : Int) (kept : Int) (i : Int) (sorted : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (Permutation input sorted)) (PreH7 : (increasing sorted)) (PreH8 : (FullPreparationSpecBridge input sorted)) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k sorted (0 : Int))) ∧ ((Znth k sorted (0 : Int)) <= n_pre)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((0 : Int) <= kept)) (PreH13 : (kept <= i)) (PreH14 : ((0 : Int) <= spent)) (PreH15 : (spent <= (i * n_pre))) (PreH16 : (PrefixGreedyState input sorted i kept spent)) ,
  (intArray.full a_pre n_pre sorted)
|--
  “ (i < n_pre) ” &&
  “ (n_pre = (Zlength (input))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((Zlength (sorted)) = n_pre) ” &&
  “ (Permutation input sorted) ” &&
  “ (increasing sorted) ” &&
  “ (FullPreparationSpecBridge input sorted) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k sorted (0 : Int))) ∧ ((Znth k sorted (0 : Int)) <= n_pre))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= kept) ” &&
  “ (kept <= i) ” &&
  “ ((0 : Int) <= spent) ” &&
  “ (spent <= (i * n_pre)) ” &&
  “ (PrefixGreedyState input sorted i kept spent) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i sorted (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre sorted)

noncomputable def solver_partial_solve_wit_3 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (spent : Int) (kept : Int) (i : Int) (sorted : (List Int)) (PreH1 : ((kept + 1) > (Znth i sorted (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (Permutation input sorted)) (PreH8 : (increasing sorted)) (PreH9 : (FullPreparationSpecBridge input sorted)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k sorted (0 : Int))) ∧ ((Znth k sorted (0 : Int)) <= n_pre)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= kept)) (PreH14 : (kept <= i)) (PreH15 : ((0 : Int) <= spent)) (PreH16 : (spent <= (i * n_pre))) (PreH17 : (PrefixGreedyState input sorted i kept spent)) ,
  (intArray.full a_pre n_pre sorted)
|--
  “ ((kept + 1) > (Znth i sorted (0 : Int))) ” &&
  “ (i < n_pre) ” &&
  “ (n_pre = (Zlength (input))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((Zlength (sorted)) = n_pre) ” &&
  “ (Permutation input sorted) ” &&
  “ (increasing sorted) ” &&
  “ (FullPreparationSpecBridge input sorted) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k sorted (0 : Int))) ∧ ((Znth k sorted (0 : Int)) <= n_pre))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= kept) ” &&
  “ (kept <= i) ” &&
  “ ((0 : Int) <= spent) ” &&
  “ (spent <= (i * n_pre)) ” &&
  “ (PrefixGreedyState input sorted i kept spent) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i sorted (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre sorted)

noncomputable def solver_partial_solve_wit_4 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (spent : Int) (kept : Int) (i : Int) (sorted : (List Int)) (PreH1 : ((kept + 1) > (Znth i sorted (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (Permutation input sorted)) (PreH8 : (increasing sorted)) (PreH9 : (FullPreparationSpecBridge input sorted)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k sorted (0 : Int))) ∧ ((Znth k sorted (0 : Int)) <= n_pre)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= kept)) (PreH14 : (kept <= i)) (PreH15 : ((0 : Int) <= spent)) (PreH16 : (spent <= (i * n_pre))) (PreH17 : (PrefixGreedyState input sorted i kept spent)) ,
  (intArray.full a_pre n_pre sorted)
|--
  “ ((kept + 1) > (Znth i sorted (0 : Int))) ” &&
  “ (i < n_pre) ” &&
  “ (n_pre = (Zlength (input))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((Zlength (sorted)) = n_pre) ” &&
  “ (Permutation input sorted) ” &&
  “ (increasing sorted) ” &&
  “ (FullPreparationSpecBridge input sorted) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k sorted (0 : Int))) ∧ ((Znth k sorted (0 : Int)) <= n_pre))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= kept) ” &&
  “ (kept <= i) ” &&
  “ ((0 : Int) <= spent) ” &&
  “ (spent <= (i * n_pre)) ” &&
  “ (PrefixGreedyState input sorted i kept spent) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i sorted (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre sorted)

noncomputable def solver_partial_solve_wit_5 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (spent : Int) (kept : Int) (i : Int) (sorted : (List Int)) (PreH1 : ((kept + 1) <= (Znth i sorted (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (Permutation input sorted)) (PreH8 : (increasing sorted)) (PreH9 : (FullPreparationSpecBridge input sorted)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k sorted (0 : Int))) ∧ ((Znth k sorted (0 : Int)) <= n_pre)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= kept)) (PreH14 : (kept <= i)) (PreH15 : ((0 : Int) <= spent)) (PreH16 : (spent <= (i * n_pre))) (PreH17 : (PrefixGreedyState input sorted i kept spent)) ,
  (intArray.full a_pre n_pre sorted)
|--
  “ ((kept + 1) <= (Znth i sorted (0 : Int))) ” &&
  “ (i < n_pre) ” &&
  “ (n_pre = (Zlength (input))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((Zlength (sorted)) = n_pre) ” &&
  “ (Permutation input sorted) ” &&
  “ (increasing sorted) ” &&
  “ (FullPreparationSpecBridge input sorted) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k sorted (0 : Int))) ∧ ((Znth k sorted (0 : Int)) <= n_pre))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= kept) ” &&
  “ (kept <= i) ” &&
  “ ((0 : Int) <= spent) ” &&
  “ (spent <= (i * n_pre)) ” &&
  “ (PrefixGreedyState input sorted i kept spent) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i sorted (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre sorted)


structure VC_Correct : Type where
  proof_of_solver_safety_wit_1 : solver_safety_wit_1
  proof_of_solver_safety_wit_2 : solver_safety_wit_2
  proof_of_solver_safety_wit_3 : solver_safety_wit_3
  proof_of_solver_safety_wit_4 : solver_safety_wit_4
  proof_of_solver_safety_wit_5 : solver_safety_wit_5
  proof_of_solver_safety_wit_6 : solver_safety_wit_6
  proof_of_solver_safety_wit_7 : solver_safety_wit_7
  proof_of_solver_safety_wit_8 : solver_safety_wit_8
  proof_of_solver_safety_wit_9 : solver_safety_wit_9
  proof_of_solver_safety_wit_10 : solver_safety_wit_10
  proof_of_solver_safety_wit_11 : solver_safety_wit_11
  proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2
  proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3
  proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4
  proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1
  proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2
  proof_of_solver_return_wit_1 : solver_return_wit_1

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version_goal
