import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P012_1139B_chocolates_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P012_1139B_chocolates_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P012_1139B_chocolates_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P012_1139B_chocolates_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (values)))) ,
  ((( &( "prev" ) )) # Int64 |->_)
  ** ((( &( "total" ) )) # Int64 |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre values)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (values)))) ,
  ((( &( "total" ) )) # Int64 |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre values)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (values)))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "prev" ) )) # Int64 |-> ((0 : Int)))
  ** ((( &( "total" ) )) # Int64 |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre values)
|--
  “ ((n_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre - 1)) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (values)))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "prev" ) )) # Int64 |-> ((0 : Int)))
  ** ((( &( "total" ) )) # Int64 |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre values)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH5 : ((-1) <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((0 : Int) <= total)) (PreH8 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH9 : ((0 : Int) <= prev)) (PreH10 : (prev <= 1000000000)) (PreH11 : (SuffixDominantState values (i + 1) total prev)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "prev" ) )) # Int64 |-> (prev))
  ** (intArray.full a_pre n_pre values)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : (i >= (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH6 : ((-1) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= total)) (PreH9 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH10 : ((0 : Int) <= prev)) (PreH11 : (prev <= 1000000000)) (PreH12 : (SuffixDominantState values (i + 1) total prev)) ,
  ((( &( "take" ) )) # Int64 |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "prev" ) )) # Int64 |-> (prev))
  ** (intArray.full a_pre n_pre values)
|--
  “ ((n_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre - 1)) ”

noncomputable def solver_safety_wit_7 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : (i >= (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH6 : ((-1) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= total)) (PreH9 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH10 : ((0 : Int) <= prev)) (PreH11 : (prev <= 1000000000)) (PreH12 : (SuffixDominantState values (i + 1) total prev)) ,
  ((( &( "take" ) )) # Int64 |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "prev" ) )) # Int64 |-> (prev))
  ** (intArray.full a_pre n_pre values)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_8 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : (i ≠ (n_pre - 1))) (PreH2 : (i >= (0 : Int))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH7 : ((-1) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= total)) (PreH10 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH11 : ((0 : Int) <= prev)) (PreH12 : (prev <= 1000000000)) (PreH13 : (SuffixDominantState values (i + 1) total prev)) ,
  ((( &( "take" ) )) # Int64 |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "prev" ) )) # Int64 |-> (prev))
  ** (intArray.full a_pre n_pre values)
|--
  “ ((prev - 1) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (prev - 1)) ”

noncomputable def solver_safety_wit_9 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : (i ≠ (n_pre - 1))) (PreH2 : (i >= (0 : Int))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH7 : ((-1) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= total)) (PreH10 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH11 : ((0 : Int) <= prev)) (PreH12 : (prev <= 1000000000)) (PreH13 : (SuffixDominantState values (i + 1) total prev)) ,
  ((( &( "take" ) )) # Int64 |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "prev" ) )) # Int64 |-> (prev))
  ** (intArray.full a_pre n_pre values)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_10 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : ((prev - 1) > (Znth i values (0 : Int)))) (PreH2 : (i ≠ (n_pre - 1))) (PreH3 : (i >= (0 : Int))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH8 : ((-1) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= total)) (PreH11 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH12 : ((0 : Int) <= prev)) (PreH13 : (prev <= 1000000000)) (PreH14 : (SuffixDominantState values (i + 1) total prev)) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "take" ) )) # Int64 |-> ((Znth i values (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "prev" ) )) # Int64 |-> (prev))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_11 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : ((prev - 1) <= (Znth i values (0 : Int)))) (PreH2 : (i ≠ (n_pre - 1))) (PreH3 : (i >= (0 : Int))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH8 : ((-1) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= total)) (PreH11 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH12 : ((0 : Int) <= prev)) (PreH13 : (prev <= 1000000000)) (PreH14 : (SuffixDominantState values (i + 1) total prev)) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "take" ) )) # Int64 |-> ((prev - 1)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "prev" ) )) # Int64 |-> (prev))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_12 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : ((Znth i values (0 : Int)) < (0 : Int))) (PreH2 : ((prev - 1) > (Znth i values (0 : Int)))) (PreH3 : (i ≠ (n_pre - 1))) (PreH4 : (i >= (0 : Int))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((0 : Int) <= total)) (PreH12 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH13 : ((0 : Int) <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1) total prev)) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "take" ) )) # Int64 |-> ((Znth i values (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "prev" ) )) # Int64 |-> (prev))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_13 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : ((prev - 1) < (0 : Int))) (PreH2 : ((prev - 1) <= (Znth i values (0 : Int)))) (PreH3 : (i ≠ (n_pre - 1))) (PreH4 : (i >= (0 : Int))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((0 : Int) <= total)) (PreH12 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH13 : ((0 : Int) <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1) total prev)) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "take" ) )) # Int64 |-> ((prev - 1)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "prev" ) )) # Int64 |-> (prev))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_14 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : (i = (n_pre - 1))) (PreH2 : (i >= (0 : Int))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH7 : ((-1) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= total)) (PreH10 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH11 : ((0 : Int) <= prev)) (PreH12 : (prev <= 1000000000)) (PreH13 : (SuffixDominantState values (i + 1) total prev)) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "take" ) )) # Int64 |-> ((Znth i values (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "prev" ) )) # Int64 |-> (prev))
|--
  “ ((total + (Znth i values (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (total + (Znth i values (0 : Int)))) ”

noncomputable def solver_safety_wit_15 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : ((Znth i values (0 : Int)) < (0 : Int))) (PreH2 : ((prev - 1) > (Znth i values (0 : Int)))) (PreH3 : (i ≠ (n_pre - 1))) (PreH4 : (i >= (0 : Int))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((0 : Int) <= total)) (PreH12 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH13 : ((0 : Int) <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1) total prev)) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "take" ) )) # Int64 |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "prev" ) )) # Int64 |-> (prev))
|--
  “ ((total + (0 : Int)) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (total + (0 : Int))) ”

noncomputable def solver_safety_wit_16 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : ((prev - 1) < (0 : Int))) (PreH2 : ((prev - 1) <= (Znth i values (0 : Int)))) (PreH3 : (i ≠ (n_pre - 1))) (PreH4 : (i >= (0 : Int))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((0 : Int) <= total)) (PreH12 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH13 : ((0 : Int) <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1) total prev)) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "take" ) )) # Int64 |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "prev" ) )) # Int64 |-> (prev))
|--
  “ ((total + (0 : Int)) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (total + (0 : Int))) ”

noncomputable def solver_safety_wit_17 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : ((Znth i values (0 : Int)) >= (0 : Int))) (PreH2 : ((prev - 1) > (Znth i values (0 : Int)))) (PreH3 : (i ≠ (n_pre - 1))) (PreH4 : (i >= (0 : Int))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((0 : Int) <= total)) (PreH12 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH13 : ((0 : Int) <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1) total prev)) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "take" ) )) # Int64 |-> ((Znth i values (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "prev" ) )) # Int64 |-> (prev))
|--
  “ ((total + (Znth i values (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (total + (Znth i values (0 : Int)))) ”

noncomputable def solver_safety_wit_18 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : ((prev - 1) >= (0 : Int))) (PreH2 : ((prev - 1) <= (Znth i values (0 : Int)))) (PreH3 : (i ≠ (n_pre - 1))) (PreH4 : (i >= (0 : Int))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((0 : Int) <= total)) (PreH12 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH13 : ((0 : Int) <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1) total prev)) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "take" ) )) # Int64 |-> ((prev - 1)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "prev" ) )) # Int64 |-> (prev))
|--
  “ ((total + (prev - 1)) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (total + (prev - 1))) ”

noncomputable def solver_safety_wit_19 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : (i = (n_pre - 1))) (PreH2 : (i >= (0 : Int))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH7 : ((-1) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= total)) (PreH10 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH11 : ((0 : Int) <= prev)) (PreH12 : (prev <= 1000000000)) (PreH13 : (SuffixDominantState values (i + 1) total prev)) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "total" ) )) # Int64 |-> ((total + (Znth i values (0 : Int)))))
  ** ((( &( "prev" ) )) # Int64 |-> ((Znth i values (0 : Int))))
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def solver_safety_wit_20 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : ((Znth i values (0 : Int)) < (0 : Int))) (PreH2 : ((prev - 1) > (Znth i values (0 : Int)))) (PreH3 : (i ≠ (n_pre - 1))) (PreH4 : (i >= (0 : Int))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((0 : Int) <= total)) (PreH12 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH13 : ((0 : Int) <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1) total prev)) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "total" ) )) # Int64 |-> ((total + (0 : Int))))
  ** ((( &( "prev" ) )) # Int64 |-> ((0 : Int)))
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def solver_safety_wit_21 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : ((prev - 1) < (0 : Int))) (PreH2 : ((prev - 1) <= (Znth i values (0 : Int)))) (PreH3 : (i ≠ (n_pre - 1))) (PreH4 : (i >= (0 : Int))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((0 : Int) <= total)) (PreH12 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH13 : ((0 : Int) <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1) total prev)) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "total" ) )) # Int64 |-> ((total + (0 : Int))))
  ** ((( &( "prev" ) )) # Int64 |-> ((0 : Int)))
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def solver_safety_wit_22 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : ((Znth i values (0 : Int)) >= (0 : Int))) (PreH2 : ((prev - 1) > (Znth i values (0 : Int)))) (PreH3 : (i ≠ (n_pre - 1))) (PreH4 : (i >= (0 : Int))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((0 : Int) <= total)) (PreH12 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH13 : ((0 : Int) <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1) total prev)) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "total" ) )) # Int64 |-> ((total + (Znth i values (0 : Int)))))
  ** ((( &( "prev" ) )) # Int64 |-> ((Znth i values (0 : Int))))
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def solver_safety_wit_23 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : ((prev - 1) >= (0 : Int))) (PreH2 : ((prev - 1) <= (Znth i values (0 : Int)))) (PreH3 : (i ≠ (n_pre - 1))) (PreH4 : (i >= (0 : Int))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((0 : Int) <= total)) (PreH12 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH13 : ((0 : Int) <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1) total prev)) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "total" ) )) # Int64 |-> ((total + (prev - 1))))
  ** ((( &( "prev" ) )) # Int64 |-> ((prev - 1)))
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (values)))) ,
  (intArray.full a_pre n_pre values)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ ((-1) <= (n_pre - 1)) ” &&
  “ ((n_pre - 1) < n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (((n_pre - (n_pre - 1)) - 1) * 1000000000)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 1000000000) ” &&
  “ (SuffixDominantState values ((n_pre - 1) + 1) (0 : Int) (0 : Int)) ”
  &&  (intArray.full a_pre n_pre values)
) \/
(
forall (values : (List Int)) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (values)))) ,
  TT && emp 
|--
  “ (SuffixDominantState values ((n_pre - 1) + 1) (0 : Int) (0 : Int)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ”
  &&  emp
)

noncomputable def solver_entail_wit_1_split_goal_1 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (values)))) ,
  (SuffixDominantState values ((n_pre - 1) + 1) (0 : Int) (0 : Int))

noncomputable def solver_entail_wit_1_split_goal_2 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (values)))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))

noncomputable def solver_entail_wit_2_1 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : (i = (n_pre - 1))) (PreH2 : (i >= (0 : Int))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH7 : ((-1) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= total)) (PreH10 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH11 : ((0 : Int) <= prev)) (PreH12 : (prev <= 1000000000)) (PreH13 : (SuffixDominantState values (i + 1) total prev)) ,
  (intArray.full a_pre n_pre values)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ ((-1) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ ((0 : Int) <= (total + (Znth i values (0 : Int)))) ” &&
  “ ((total + (Znth i values (0 : Int))) <= (((n_pre - (i - 1)) - 1) * 1000000000)) ” &&
  “ ((0 : Int) <= (Znth i values (0 : Int))) ” &&
  “ ((Znth i values (0 : Int)) <= 1000000000) ” &&
  “ (SuffixDominantState values ((i - 1) + 1) (total + (Znth i values (0 : Int))) (Znth i values (0 : Int))) ”
  &&  (intArray.full a_pre n_pre values)
) \/
(
forall (values : (List Int)) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : (i = (n_pre - 1))) (PreH2 : (i >= (0 : Int))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH7 : ((-1) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= total)) (PreH10 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH11 : ((0 : Int) <= prev)) (PreH12 : (prev <= 1000000000)) (PreH13 : (SuffixDominantState values (i + 1) total prev)) ,
  TT && emp 
|--
  “ (SuffixDominantState values (((n_pre - 1) - 1) + 1) (total + (Znth (n_pre - 1) values (0 : Int))) (Znth (n_pre - 1) values (0 : Int))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_1_split_goal_1 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : (i = (n_pre - 1))) (PreH2 : (i >= (0 : Int))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH7 : ((-1) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= total)) (PreH10 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH11 : ((0 : Int) <= prev)) (PreH12 : (prev <= 1000000000)) (PreH13 : (SuffixDominantState values (i + 1) total prev)) ,
  (SuffixDominantState values (((n_pre - 1) - 1) + 1) (total + (Znth (n_pre - 1) values (0 : Int))) (Znth (n_pre - 1) values (0 : Int)))

noncomputable def solver_entail_wit_2_2 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : ((Znth i values (0 : Int)) < (0 : Int))) (PreH2 : ((prev - 1) > (Znth i values (0 : Int)))) (PreH3 : (i ≠ (n_pre - 1))) (PreH4 : (i >= (0 : Int))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((0 : Int) <= total)) (PreH12 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH13 : ((0 : Int) <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1) total prev)) ,
  (intArray.full a_pre n_pre values)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ ((-1) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ ((0 : Int) <= (total + (0 : Int))) ” &&
  “ ((total + (0 : Int)) <= (((n_pre - (i - 1)) - 1) * 1000000000)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 1000000000) ” &&
  “ (SuffixDominantState values ((i - 1) + 1) (total + (0 : Int)) (0 : Int)) ”
  &&  (intArray.full a_pre n_pre values)
) \/
(
forall (values : (List Int)) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : ((Znth i values (0 : Int)) < (0 : Int))) (PreH2 : ((prev - 1) > (Znth i values (0 : Int)))) (PreH3 : (i ≠ (n_pre - 1))) (PreH4 : (i >= (0 : Int))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((0 : Int) <= total)) (PreH12 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH13 : ((0 : Int) <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1) total prev)) ,
  TT && emp 
|--
  “ (SuffixDominantState values ((i - 1) + 1) (total + (0 : Int)) (0 : Int)) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_2_split_goal_1 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : ((Znth i values (0 : Int)) < (0 : Int))) (PreH2 : ((prev - 1) > (Znth i values (0 : Int)))) (PreH3 : (i ≠ (n_pre - 1))) (PreH4 : (i >= (0 : Int))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((0 : Int) <= total)) (PreH12 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH13 : ((0 : Int) <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1) total prev)) ,
  (SuffixDominantState values ((i - 1) + 1) (total + (0 : Int)) (0 : Int))

noncomputable def solver_entail_wit_2_3 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : ((prev - 1) < (0 : Int))) (PreH2 : ((prev - 1) <= (Znth i values (0 : Int)))) (PreH3 : (i ≠ (n_pre - 1))) (PreH4 : (i >= (0 : Int))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((0 : Int) <= total)) (PreH12 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH13 : ((0 : Int) <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1) total prev)) ,
  (intArray.full a_pre n_pre values)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ ((-1) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ ((0 : Int) <= (total + (0 : Int))) ” &&
  “ ((total + (0 : Int)) <= (((n_pre - (i - 1)) - 1) * 1000000000)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 1000000000) ” &&
  “ (SuffixDominantState values ((i - 1) + 1) (total + (0 : Int)) (0 : Int)) ”
  &&  (intArray.full a_pre n_pre values)
) \/
(
forall (values : (List Int)) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : ((prev - 1) < (0 : Int))) (PreH2 : ((prev - 1) <= (Znth i values (0 : Int)))) (PreH3 : (i ≠ (n_pre - 1))) (PreH4 : (i >= (0 : Int))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((0 : Int) <= total)) (PreH12 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH13 : ((0 : Int) <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1) total prev)) ,
  TT && emp 
|--
  “ (SuffixDominantState values ((i - 1) + 1) (total + (0 : Int)) (0 : Int)) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_3_split_goal_1 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : ((prev - 1) < (0 : Int))) (PreH2 : ((prev - 1) <= (Znth i values (0 : Int)))) (PreH3 : (i ≠ (n_pre - 1))) (PreH4 : (i >= (0 : Int))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((0 : Int) <= total)) (PreH12 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH13 : ((0 : Int) <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1) total prev)) ,
  (SuffixDominantState values ((i - 1) + 1) (total + (0 : Int)) (0 : Int))

noncomputable def solver_entail_wit_2_4 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : ((Znth i values (0 : Int)) >= (0 : Int))) (PreH2 : ((prev - 1) > (Znth i values (0 : Int)))) (PreH3 : (i ≠ (n_pre - 1))) (PreH4 : (i >= (0 : Int))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((0 : Int) <= total)) (PreH12 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH13 : ((0 : Int) <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1) total prev)) ,
  (intArray.full a_pre n_pre values)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ ((-1) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ ((0 : Int) <= (total + (Znth i values (0 : Int)))) ” &&
  “ ((total + (Znth i values (0 : Int))) <= (((n_pre - (i - 1)) - 1) * 1000000000)) ” &&
  “ ((0 : Int) <= (Znth i values (0 : Int))) ” &&
  “ ((Znth i values (0 : Int)) <= 1000000000) ” &&
  “ (SuffixDominantState values ((i - 1) + 1) (total + (Znth i values (0 : Int))) (Znth i values (0 : Int))) ”
  &&  (intArray.full a_pre n_pre values)
) \/
(
forall (values : (List Int)) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : ((Znth i values (0 : Int)) >= (0 : Int))) (PreH2 : ((prev - 1) > (Znth i values (0 : Int)))) (PreH3 : (i ≠ (n_pre - 1))) (PreH4 : (i >= (0 : Int))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((0 : Int) <= total)) (PreH12 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH13 : ((0 : Int) <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1) total prev)) ,
  TT && emp 
|--
  “ (SuffixDominantState values ((i - 1) + 1) (total + (Znth i values (0 : Int))) (Znth i values (0 : Int))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_4_split_goal_1 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : ((Znth i values (0 : Int)) >= (0 : Int))) (PreH2 : ((prev - 1) > (Znth i values (0 : Int)))) (PreH3 : (i ≠ (n_pre - 1))) (PreH4 : (i >= (0 : Int))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((0 : Int) <= total)) (PreH12 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH13 : ((0 : Int) <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1) total prev)) ,
  (SuffixDominantState values ((i - 1) + 1) (total + (Znth i values (0 : Int))) (Znth i values (0 : Int)))

noncomputable def solver_entail_wit_2_5 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : ((prev - 1) >= (0 : Int))) (PreH2 : ((prev - 1) <= (Znth i values (0 : Int)))) (PreH3 : (i ≠ (n_pre - 1))) (PreH4 : (i >= (0 : Int))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((0 : Int) <= total)) (PreH12 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH13 : ((0 : Int) <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1) total prev)) ,
  (intArray.full a_pre n_pre values)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ ((-1) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ ((0 : Int) <= (total + (prev - 1))) ” &&
  “ ((total + (prev - 1)) <= (((n_pre - (i - 1)) - 1) * 1000000000)) ” &&
  “ ((0 : Int) <= (prev - 1)) ” &&
  “ ((prev - 1) <= 1000000000) ” &&
  “ (SuffixDominantState values ((i - 1) + 1) (total + (prev - 1)) (prev - 1)) ”
  &&  (intArray.full a_pre n_pre values)
) \/
(
forall (values : (List Int)) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : ((prev - 1) >= (0 : Int))) (PreH2 : ((prev - 1) <= (Znth i values (0 : Int)))) (PreH3 : (i ≠ (n_pre - 1))) (PreH4 : (i >= (0 : Int))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((0 : Int) <= total)) (PreH12 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH13 : ((0 : Int) <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1) total prev)) ,
  TT && emp 
|--
  “ (SuffixDominantState values ((i - 1) + 1) (total + (prev - 1)) (prev - 1)) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_5_split_goal_1 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : ((prev - 1) >= (0 : Int))) (PreH2 : ((prev - 1) <= (Znth i values (0 : Int)))) (PreH3 : (i ≠ (n_pre - 1))) (PreH4 : (i >= (0 : Int))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH9 : ((-1) <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((0 : Int) <= total)) (PreH12 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH13 : ((0 : Int) <= prev)) (PreH14 : (prev <= 1000000000)) (PreH15 : (SuffixDominantState values (i + 1) total prev)) ,
  (SuffixDominantState values ((i - 1) + 1) (total + (prev - 1)) (prev - 1))

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : (i < (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH6 : ((-1) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= total)) (PreH9 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH10 : ((0 : Int) <= prev)) (PreH11 : (prev <= 1000000000)) (PreH12 : (SuffixDominantState values (i + 1) total prev)) ,
  (intArray.full a_pre n_pre values)
|--
  “ (Spec values total) ”
  &&  (intArray.full a_pre n_pre values)
) \/
(
forall (values : (List Int)) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : (i < (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH6 : ((-1) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= total)) (PreH9 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH10 : ((0 : Int) <= prev)) (PreH11 : (prev <= 1000000000)) (PreH12 : (SuffixDominantState values (i + 1) total prev)) ,
  TT && emp 
|--
  “ (Spec values total) ”
  &&  emp
)

noncomputable def solver_return_wit_1_split_goal_1 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : (i < (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH6 : ((-1) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= total)) (PreH9 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH10 : ((0 : Int) <= prev)) (PreH11 : (prev <= 1000000000)) (PreH12 : (SuffixDominantState values (i + 1) total prev)) ,
  (Spec values total)

noncomputable def solver_partial_solve_wit_1 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : (i = (n_pre - 1))) (PreH2 : (i >= (0 : Int))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH7 : ((-1) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= total)) (PreH10 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH11 : ((0 : Int) <= prev)) (PreH12 : (prev <= 1000000000)) (PreH13 : (SuffixDominantState values (i + 1) total prev)) ,
  (intArray.full a_pre n_pre values)
|--
  “ (i = (n_pre - 1)) ” &&
  “ (i >= (0 : Int)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ ((-1) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= (((n_pre - i) - 1) * 1000000000)) ” &&
  “ ((0 : Int) <= prev) ” &&
  “ (prev <= 1000000000) ” &&
  “ (SuffixDominantState values (i + 1) total prev) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i values (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre values)

noncomputable def solver_partial_solve_wit_2 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : (i ≠ (n_pre - 1))) (PreH2 : (i >= (0 : Int))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH7 : ((-1) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= total)) (PreH10 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH11 : ((0 : Int) <= prev)) (PreH12 : (prev <= 1000000000)) (PreH13 : (SuffixDominantState values (i + 1) total prev)) ,
  (intArray.full a_pre n_pre values)
|--
  “ (i ≠ (n_pre - 1)) ” &&
  “ (i >= (0 : Int)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ ((-1) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= (((n_pre - i) - 1) * 1000000000)) ” &&
  “ ((0 : Int) <= prev) ” &&
  “ (prev <= 1000000000) ” &&
  “ (SuffixDominantState values (i + 1) total prev) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i values (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre values)

noncomputable def solver_partial_solve_wit_3 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (prev : Int) (total : Int) (i : Int) (PreH1 : ((prev - 1) > (Znth i values (0 : Int)))) (PreH2 : (i ≠ (n_pre - 1))) (PreH3 : (i >= (0 : Int))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000)))) (PreH8 : ((-1) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= total)) (PreH11 : (total <= (((n_pre - i) - 1) * 1000000000))) (PreH12 : ((0 : Int) <= prev)) (PreH13 : (prev <= 1000000000)) (PreH14 : (SuffixDominantState values (i + 1) total prev)) ,
  (intArray.full a_pre n_pre values)
|--
  “ ((prev - 1) > (Znth i values (0 : Int))) ” &&
  “ (i ≠ (n_pre - 1)) ” &&
  “ (i >= (0 : Int)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 1000000000))) ” &&
  “ ((-1) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= (((n_pre - i) - 1) * 1000000000)) ” &&
  “ ((0 : Int) <= prev) ” &&
  “ (prev <= 1000000000) ” &&
  “ (SuffixDominantState values (i + 1) total prev) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i values (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre values)


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
  proof_of_solver_safety_wit_12 : solver_safety_wit_12
  proof_of_solver_safety_wit_13 : solver_safety_wit_13
  proof_of_solver_safety_wit_14 : solver_safety_wit_14
  proof_of_solver_safety_wit_15 : solver_safety_wit_15
  proof_of_solver_safety_wit_16 : solver_safety_wit_16
  proof_of_solver_safety_wit_17 : solver_safety_wit_17
  proof_of_solver_safety_wit_18 : solver_safety_wit_18
  proof_of_solver_safety_wit_19 : solver_safety_wit_19
  proof_of_solver_safety_wit_20 : solver_safety_wit_20
  proof_of_solver_safety_wit_21 : solver_safety_wit_21
  proof_of_solver_safety_wit_22 : solver_safety_wit_22
  proof_of_solver_safety_wit_23 : solver_safety_wit_23
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2
  proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1
  proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2
  proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3
  proof_of_solver_entail_wit_2_4 : solver_entail_wit_2_4
  proof_of_solver_entail_wit_2_5 : solver_entail_wit_2_5
  proof_of_solver_return_wit_1 : solver_return_wit_1

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P012_1139B_chocolates_goal
