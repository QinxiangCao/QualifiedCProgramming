import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P030_1113B_sasha_and_magnetic_machines_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P030_1113B_sasha_and_magnetic_machines_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P030_1113B_sasha_and_magnetic_machines_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P030_1113B_sasha_and_magnetic_machines_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (PreH1 : (2 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 50000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> ((1 <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 100)))) (PreH4 : (n_pre = (Zlength (values)))) ,
  ((( &( "sum" ) )) # Int |->_)
  ** ((( &( "mn" ) )) # Int |-> (101))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre values)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (PreH1 : (2 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 50000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> ((1 <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 100)))) (PreH4 : (n_pre = (Zlength (values)))) ,
  ((( &( "mn" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre values)
|--
  “ (101 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 101) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (PreH1 : (2 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 50000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> ((1 <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 100)))) (PreH4 : (n_pre = (Zlength (values)))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "sum" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "mn" ) )) # Int |-> (101))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre values)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (mn : Int) (sum : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= sum)) (PreH9 : (sum <= (100 * i))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 101)) (PreH12 : (PrefixSummary values i sum mn)) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "sum" ) )) # Int |-> (sum))
  ** ((( &( "mn" ) )) # Int |-> (mn))
|--
  “ ((sum + (Znth i values (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (sum + (Znth i values (0 : Int)))) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (mn : Int) (sum : Int) (i : Int) (PreH1 : ((Znth i values (0 : Int)) < mn)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= sum)) (PreH10 : (sum <= (100 * i))) (PreH11 : (1 <= mn)) (PreH12 : (mn <= 101)) (PreH13 : (PrefixSummary values i sum mn)) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "sum" ) )) # Int |-> ((sum + (Znth i values (0 : Int)))))
  ** ((( &( "mn" ) )) # Int |-> ((Znth i values (0 : Int))))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (mn : Int) (sum : Int) (i : Int) (PreH1 : ((Znth i values (0 : Int)) >= mn)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= sum)) (PreH10 : (sum <= (100 * i))) (PreH11 : (1 <= mn)) (PreH12 : (mn <= 101)) (PreH13 : (PrefixSummary values i sum mn)) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "sum" ) )) # Int |-> ((sum + (Znth i values (0 : Int)))))
  ** ((( &( "mn" ) )) # Int |-> (mn))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_7 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (mn : Int) (sum : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= sum)) (PreH9 : (sum <= (100 * i))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 101)) (PreH12 : (PrefixSummary values i sum mn)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "answer" ) )) # Int |-> (sum))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "sum" ) )) # Int |-> (sum))
  ** ((( &( "mn" ) )) # Int |-> (mn))
  ** (intArray.full a_pre n_pre values)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_8 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (i < n_pre)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= answer)) (PreH14 : (answer <= sum)) (PreH15 : (SearchMinimum values sum mn i 2 answer)) ,
  ((( &( "x" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "mn" ) )) # Int |-> (mn))
  ** ((( &( "sum" ) )) # Int |-> (sum))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full a_pre n_pre values)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_9 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (x <= (Znth i values (0 : Int)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH15 : ((0 : Int) <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer)) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "mn" ) )) # Int |-> (mn))
  ** ((( &( "sum" ) )) # Int |-> (sum))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "answer" ) )) # Int |-> (answer))
|--
  “ (((Znth i values (0 : Int)) ≠ (INT_MIN)) ∨ (x ≠ (-1))) ” &&
  “ (x ≠ (0 : Int)) ”

noncomputable def solver_safety_wit_10 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (x <= (Znth i values (0 : Int)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH15 : ((0 : Int) <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer)) (PreH18 : ((Z.rem (Znth i values (0 : Int)) x) = (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "mn" ) )) # Int |-> (mn))
  ** ((( &( "sum" ) )) # Int |-> (sum))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "answer" ) )) # Int |-> (answer))
|--
  “ (((((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x)) + (mn * x)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x)) + (mn * x))) ”
) \/
(
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (x <= (Znth i values (0 : Int)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH15 : ((0 : Int) <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer)) (PreH18 : ((Z.rem (Znth i values (0 : Int)) x) = (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "mn" ) )) # Int |-> (mn))
  ** ((( &( "sum" ) )) # Int |-> (sum))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "answer" ) )) # Int |-> (answer))
|--
  “ (((((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x)) + (mn * x)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x)) + (mn * x))) ”
)

noncomputable def solver_safety_wit_10_split_goal_1 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (x <= (Znth i values (0 : Int)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH15 : ((0 : Int) <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer)) (PreH18 : ((Z.rem (Znth i values (0 : Int)) x) = (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "mn" ) )) # Int |-> (mn))
  ** ((( &( "sum" ) )) # Int |-> (sum))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "answer" ) )) # Int |-> (answer))
|--
  “ (((((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x)) + (mn * x)) <= INT_MAX) ”

noncomputable def solver_safety_wit_10_split_goal_2 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (x <= (Znth i values (0 : Int)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH15 : ((0 : Int) <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer)) (PreH18 : ((Z.rem (Znth i values (0 : Int)) x) = (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "mn" ) )) # Int |-> (mn))
  ** ((( &( "sum" ) )) # Int |-> (sum))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "answer" ) )) # Int |-> (answer))
|--
  “ ((INT_MIN) <= ((((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x)) + (mn * x))) ”

noncomputable def solver_safety_wit_11 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (x <= (Znth i values (0 : Int)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH15 : ((0 : Int) <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer)) (PreH18 : ((Z.rem (Znth i values (0 : Int)) x) = (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "mn" ) )) # Int |-> (mn))
  ** ((( &( "sum" ) )) # Int |-> (sum))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "answer" ) )) # Int |-> (answer))
|--
  “ ((mn * x) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (mn * x)) ”
) \/
(
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (x <= (Znth i values (0 : Int)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH15 : ((0 : Int) <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer)) (PreH18 : ((Z.rem (Znth i values (0 : Int)) x) = (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "mn" ) )) # Int |-> (mn))
  ** ((( &( "sum" ) )) # Int |-> (sum))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "answer" ) )) # Int |-> (answer))
|--
  “ ((mn * x) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (mn * x)) ”
)

noncomputable def solver_safety_wit_11_split_goal_1 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (x <= (Znth i values (0 : Int)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH15 : ((0 : Int) <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer)) (PreH18 : ((Z.rem (Znth i values (0 : Int)) x) = (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "mn" ) )) # Int |-> (mn))
  ** ((( &( "sum" ) )) # Int |-> (sum))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "answer" ) )) # Int |-> (answer))
|--
  “ ((mn * x) <= INT_MAX) ”

noncomputable def solver_safety_wit_11_split_goal_2 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (x <= (Znth i values (0 : Int)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH15 : ((0 : Int) <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer)) (PreH18 : ((Z.rem (Znth i values (0 : Int)) x) = (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "mn" ) )) # Int |-> (mn))
  ** ((( &( "sum" ) )) # Int |-> (sum))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "answer" ) )) # Int |-> (answer))
|--
  “ ((INT_MIN) <= (mn * x)) ”

noncomputable def solver_safety_wit_12 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (x <= (Znth i values (0 : Int)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH15 : ((0 : Int) <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer)) (PreH18 : ((Z.rem (Znth i values (0 : Int)) x) = (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "mn" ) )) # Int |-> (mn))
  ** ((( &( "sum" ) )) # Int |-> (sum))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "answer" ) )) # Int |-> (answer))
|--
  “ ((((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x))) ”
) \/
(
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (x <= (Znth i values (0 : Int)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH15 : ((0 : Int) <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer)) (PreH18 : ((Z.rem (Znth i values (0 : Int)) x) = (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "mn" ) )) # Int |-> (mn))
  ** ((( &( "sum" ) )) # Int |-> (sum))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "answer" ) )) # Int |-> (answer))
|--
  “ ((((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x))) ”
)

noncomputable def solver_safety_wit_12_split_goal_1 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (x <= (Znth i values (0 : Int)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH15 : ((0 : Int) <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer)) (PreH18 : ((Z.rem (Znth i values (0 : Int)) x) = (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "mn" ) )) # Int |-> (mn))
  ** ((( &( "sum" ) )) # Int |-> (sum))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "answer" ) )) # Int |-> (answer))
|--
  “ ((((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x)) <= INT_MAX) ”

noncomputable def solver_safety_wit_12_split_goal_2 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (x <= (Znth i values (0 : Int)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH15 : ((0 : Int) <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer)) (PreH18 : ((Z.rem (Znth i values (0 : Int)) x) = (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "mn" ) )) # Int |-> (mn))
  ** ((( &( "sum" ) )) # Int |-> (sum))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "answer" ) )) # Int |-> (answer))
|--
  “ ((INT_MIN) <= (((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x))) ”

noncomputable def solver_safety_wit_13 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (x <= (Znth i values (0 : Int)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH15 : ((0 : Int) <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer)) (PreH18 : ((Z.rem (Znth i values (0 : Int)) x) = (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "mn" ) )) # Int |-> (mn))
  ** ((( &( "sum" ) )) # Int |-> (sum))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "answer" ) )) # Int |-> (answer))
|--
  “ (((Znth i values (0 : Int)) ≠ (INT_MIN)) ∨ (x ≠ (-1))) ” &&
  “ (x ≠ (0 : Int)) ”

noncomputable def solver_safety_wit_14 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (x <= (Znth i values (0 : Int)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH15 : ((0 : Int) <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer)) (PreH18 : ((Z.rem (Znth i values (0 : Int)) x) = (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "mn" ) )) # Int |-> (mn))
  ** ((( &( "sum" ) )) # Int |-> (sum))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "answer" ) )) # Int |-> (answer))
|--
  “ (((sum - (Znth i values (0 : Int))) - mn) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((sum - (Znth i values (0 : Int))) - mn)) ”

noncomputable def solver_safety_wit_15 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (x <= (Znth i values (0 : Int)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH15 : ((0 : Int) <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer)) (PreH18 : ((Z.rem (Znth i values (0 : Int)) x) = (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "mn" ) )) # Int |-> (mn))
  ** ((( &( "sum" ) )) # Int |-> (sum))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "answer" ) )) # Int |-> (answer))
|--
  “ ((sum - (Znth i values (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (sum - (Znth i values (0 : Int)))) ”

noncomputable def solver_safety_wit_16 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (((((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x)) + (mn * x)) < answer)) (PreH2 : (x <= (Znth i values (0 : Int)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (PrefixSummary values n_pre sum mn)) (PreH8 : ((0 : Int) <= sum)) (PreH9 : (sum <= (100 * n_pre))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 100)) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : (2 <= x)) (PreH15 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer <= sum)) (PreH18 : (SearchMinimum values sum mn i x answer)) (PreH19 : ((Z.rem (Znth i values (0 : Int)) x) = (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "mn" ) )) # Int |-> (mn))
  ** ((( &( "sum" ) )) # Int |-> (sum))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "answer" ) )) # Int |-> (((((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x)) + (mn * x))))
|--
  “ ((x + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (x + 1)) ”
) \/
(
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (((((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x)) + (mn * x)) < answer)) (PreH2 : (x <= (Znth i values (0 : Int)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (PrefixSummary values n_pre sum mn)) (PreH8 : ((0 : Int) <= sum)) (PreH9 : (sum <= (100 * n_pre))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 100)) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : (2 <= x)) (PreH15 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer <= sum)) (PreH18 : (SearchMinimum values sum mn i x answer)) (PreH19 : ((Z.rem (Znth i values (0 : Int)) x) = (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "mn" ) )) # Int |-> (mn))
  ** ((( &( "sum" ) )) # Int |-> (sum))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "answer" ) )) # Int |-> (((((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x)) + (mn * x))))
|--
  “ ((x + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (x + 1)) ”
)

noncomputable def solver_safety_wit_16_split_goal_1 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (((((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x)) + (mn * x)) < answer)) (PreH2 : (x <= (Znth i values (0 : Int)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (PrefixSummary values n_pre sum mn)) (PreH8 : ((0 : Int) <= sum)) (PreH9 : (sum <= (100 * n_pre))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 100)) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : (2 <= x)) (PreH15 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer <= sum)) (PreH18 : (SearchMinimum values sum mn i x answer)) (PreH19 : ((Z.rem (Znth i values (0 : Int)) x) = (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "mn" ) )) # Int |-> (mn))
  ** ((( &( "sum" ) )) # Int |-> (sum))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "answer" ) )) # Int |-> (((((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x)) + (mn * x))))
|--
  “ ((x + 1) <= INT_MAX) ”

noncomputable def solver_safety_wit_16_split_goal_2 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (((((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x)) + (mn * x)) < answer)) (PreH2 : (x <= (Znth i values (0 : Int)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (PrefixSummary values n_pre sum mn)) (PreH8 : ((0 : Int) <= sum)) (PreH9 : (sum <= (100 * n_pre))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 100)) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : (2 <= x)) (PreH15 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer <= sum)) (PreH18 : (SearchMinimum values sum mn i x answer)) (PreH19 : ((Z.rem (Znth i values (0 : Int)) x) = (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "mn" ) )) # Int |-> (mn))
  ** ((( &( "sum" ) )) # Int |-> (sum))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "answer" ) )) # Int |-> (((((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x)) + (mn * x))))
|--
  “ ((INT_MIN) <= (x + 1)) ”

noncomputable def solver_safety_wit_17 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (((((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x)) + (mn * x)) >= answer)) (PreH2 : (x <= (Znth i values (0 : Int)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (PrefixSummary values n_pre sum mn)) (PreH8 : ((0 : Int) <= sum)) (PreH9 : (sum <= (100 * n_pre))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 100)) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : (2 <= x)) (PreH15 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer <= sum)) (PreH18 : (SearchMinimum values sum mn i x answer)) (PreH19 : ((Z.rem (Znth i values (0 : Int)) x) = (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "mn" ) )) # Int |-> (mn))
  ** ((( &( "sum" ) )) # Int |-> (sum))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "answer" ) )) # Int |-> (answer))
|--
  “ ((x + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (x + 1)) ”
) \/
(
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (((((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x)) + (mn * x)) >= answer)) (PreH2 : (x <= (Znth i values (0 : Int)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (PrefixSummary values n_pre sum mn)) (PreH8 : ((0 : Int) <= sum)) (PreH9 : (sum <= (100 * n_pre))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 100)) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : (2 <= x)) (PreH15 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer <= sum)) (PreH18 : (SearchMinimum values sum mn i x answer)) (PreH19 : ((Z.rem (Znth i values (0 : Int)) x) = (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "mn" ) )) # Int |-> (mn))
  ** ((( &( "sum" ) )) # Int |-> (sum))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "answer" ) )) # Int |-> (answer))
|--
  “ ((x + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (x + 1)) ”
)

noncomputable def solver_safety_wit_17_split_goal_1 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (((((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x)) + (mn * x)) >= answer)) (PreH2 : (x <= (Znth i values (0 : Int)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (PrefixSummary values n_pre sum mn)) (PreH8 : ((0 : Int) <= sum)) (PreH9 : (sum <= (100 * n_pre))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 100)) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : (2 <= x)) (PreH15 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer <= sum)) (PreH18 : (SearchMinimum values sum mn i x answer)) (PreH19 : ((Z.rem (Znth i values (0 : Int)) x) = (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "mn" ) )) # Int |-> (mn))
  ** ((( &( "sum" ) )) # Int |-> (sum))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "answer" ) )) # Int |-> (answer))
|--
  “ ((x + 1) <= INT_MAX) ”

noncomputable def solver_safety_wit_17_split_goal_2 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (((((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x)) + (mn * x)) >= answer)) (PreH2 : (x <= (Znth i values (0 : Int)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (PrefixSummary values n_pre sum mn)) (PreH8 : ((0 : Int) <= sum)) (PreH9 : (sum <= (100 * n_pre))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 100)) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : (2 <= x)) (PreH15 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer <= sum)) (PreH18 : (SearchMinimum values sum mn i x answer)) (PreH19 : ((Z.rem (Znth i values (0 : Int)) x) = (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "mn" ) )) # Int |-> (mn))
  ** ((( &( "sum" ) )) # Int |-> (sum))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "answer" ) )) # Int |-> (answer))
|--
  “ ((INT_MIN) <= (x + 1)) ”

noncomputable def solver_safety_wit_18 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (x <= (Znth i values (0 : Int)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH15 : ((0 : Int) <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer)) (PreH18 : ((Z.rem (Znth i values (0 : Int)) x) ≠ (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "mn" ) )) # Int |-> (mn))
  ** ((( &( "sum" ) )) # Int |-> (sum))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "answer" ) )) # Int |-> (answer))
|--
  “ ((x + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (x + 1)) ”
) \/
(
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (x <= (Znth i values (0 : Int)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH15 : ((0 : Int) <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer)) (PreH18 : ((Z.rem (Znth i values (0 : Int)) x) ≠ (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "mn" ) )) # Int |-> (mn))
  ** ((( &( "sum" ) )) # Int |-> (sum))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "answer" ) )) # Int |-> (answer))
|--
  “ ((x + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (x + 1)) ”
)

noncomputable def solver_safety_wit_18_split_goal_1 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (x <= (Znth i values (0 : Int)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH15 : ((0 : Int) <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer)) (PreH18 : ((Z.rem (Znth i values (0 : Int)) x) ≠ (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "mn" ) )) # Int |-> (mn))
  ** ((( &( "sum" ) )) # Int |-> (sum))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "answer" ) )) # Int |-> (answer))
|--
  “ ((x + 1) <= INT_MAX) ”

noncomputable def solver_safety_wit_18_split_goal_2 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (x <= (Znth i values (0 : Int)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH15 : ((0 : Int) <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer)) (PreH18 : ((Z.rem (Znth i values (0 : Int)) x) ≠ (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "mn" ) )) # Int |-> (mn))
  ** ((( &( "sum" ) )) # Int |-> (sum))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "answer" ) )) # Int |-> (answer))
|--
  “ ((INT_MIN) <= (x + 1)) ”

noncomputable def solver_safety_wit_19 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (x > (Znth i values (0 : Int)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH15 : ((0 : Int) <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer)) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "mn" ) )) # Int |-> (mn))
  ** ((( &( "sum" ) )) # Int |-> (sum))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int |-> (answer))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (PreH1 : (2 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 50000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> ((1 <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 100)))) (PreH4 : (n_pre = (Zlength (values)))) ,
  (intArray.full a_pre n_pre values)
|--
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 50000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100))) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (100 * (0 : Int))) ” &&
  “ (1 <= 101) ” &&
  “ (101 <= 101) ” &&
  “ (PrefixSummary values (0 : Int) (0 : Int) 101) ”
  &&  (intArray.full a_pre n_pre values)
) \/
(
forall (values : (List Int)) (n_pre : Int) (PreH1 : (2 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 50000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> ((1 <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 100)))) (PreH4 : (n_pre = (Zlength (values)))) ,
  TT && emp 
|--
  “ (PrefixSummary values (0 : Int) (0 : Int) 101) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100))) ”
  &&  emp
)

noncomputable def solver_entail_wit_1_split_goal_1 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (PreH1 : (2 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 50000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> ((1 <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 100)))) (PreH4 : (n_pre = (Zlength (values)))) ,
  (PrefixSummary values (0 : Int) (0 : Int) 101)

noncomputable def solver_entail_wit_1_split_goal_2 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (PreH1 : (2 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 50000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> ((1 <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 100)))) (PreH4 : (n_pre = (Zlength (values)))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))

noncomputable def solver_entail_wit_2_1 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (mn : Int) (sum : Int) (i : Int) (PreH1 : ((Znth i values (0 : Int)) < mn)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= sum)) (PreH10 : (sum <= (100 * i))) (PreH11 : (1 <= mn)) (PreH12 : (mn <= 101)) (PreH13 : (PrefixSummary values i sum mn)) ,
  (intArray.full a_pre n_pre values)
|--
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 50000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100))) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= (sum + (Znth i values (0 : Int)))) ” &&
  “ ((sum + (Znth i values (0 : Int))) <= (100 * (i + 1))) ” &&
  “ (1 <= (Znth i values (0 : Int))) ” &&
  “ ((Znth i values (0 : Int)) <= 101) ” &&
  “ (PrefixSummary values (i + 1) (sum + (Znth i values (0 : Int))) (Znth i values (0 : Int))) ”
  &&  (intArray.full a_pre n_pre values)
) \/
(
forall (values : (List Int)) (n_pre : Int) (mn : Int) (sum : Int) (i : Int) (PreH1 : ((Znth i values (0 : Int)) < mn)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= sum)) (PreH10 : (sum <= (100 * i))) (PreH11 : (1 <= mn)) (PreH12 : (mn <= 101)) (PreH13 : (PrefixSummary values i sum mn)) ,
  TT && emp 
|--
  “ (PrefixSummary values (i + 1) (sum + (Znth i values (0 : Int))) (Znth i values (0 : Int))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_1_split_goal_1 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (mn : Int) (sum : Int) (i : Int) (PreH1 : ((Znth i values (0 : Int)) < mn)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= sum)) (PreH10 : (sum <= (100 * i))) (PreH11 : (1 <= mn)) (PreH12 : (mn <= 101)) (PreH13 : (PrefixSummary values i sum mn)) ,
  (PrefixSummary values (i + 1) (sum + (Znth i values (0 : Int))) (Znth i values (0 : Int)))

noncomputable def solver_entail_wit_2_2 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (mn : Int) (sum : Int) (i : Int) (PreH1 : ((Znth i values (0 : Int)) >= mn)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= sum)) (PreH10 : (sum <= (100 * i))) (PreH11 : (1 <= mn)) (PreH12 : (mn <= 101)) (PreH13 : (PrefixSummary values i sum mn)) ,
  (intArray.full a_pre n_pre values)
|--
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 50000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100))) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= (sum + (Znth i values (0 : Int)))) ” &&
  “ ((sum + (Znth i values (0 : Int))) <= (100 * (i + 1))) ” &&
  “ (1 <= mn) ” &&
  “ (mn <= 101) ” &&
  “ (PrefixSummary values (i + 1) (sum + (Znth i values (0 : Int))) mn) ”
  &&  (intArray.full a_pre n_pre values)
) \/
(
forall (values : (List Int)) (n_pre : Int) (mn : Int) (sum : Int) (i : Int) (PreH1 : ((Znth i values (0 : Int)) >= mn)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= sum)) (PreH10 : (sum <= (100 * i))) (PreH11 : (1 <= mn)) (PreH12 : (mn <= 101)) (PreH13 : (PrefixSummary values i sum mn)) ,
  TT && emp 
|--
  “ (PrefixSummary values (i + 1) (sum + (Znth i values (0 : Int))) mn) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_2_split_goal_1 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (mn : Int) (sum : Int) (i : Int) (PreH1 : ((Znth i values (0 : Int)) >= mn)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= sum)) (PreH10 : (sum <= (100 * i))) (PreH11 : (1 <= mn)) (PreH12 : (mn <= 101)) (PreH13 : (PrefixSummary values i sum mn)) ,
  (PrefixSummary values (i + 1) (sum + (Znth i values (0 : Int))) mn)

noncomputable def solver_entail_wit_3 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (mn : Int) (sum : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values (0 : Int))) ∧ ((Znth k_2 values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= sum)) (PreH9 : (sum <= (100 * i))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 101)) (PreH12 : (PrefixSummary values i sum mn)) ,
  (intArray.full a_pre n_pre values)
|--
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 50000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100))) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ (PrefixSummary values n_pre sum mn) ” &&
  “ ((0 : Int) <= sum) ” &&
  “ (sum <= (100 * n_pre)) ” &&
  “ (1 <= mn) ” &&
  “ (mn <= 100) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= sum) ” &&
  “ (sum <= sum) ” &&
  “ (SearchMinimum values sum mn (0 : Int) 2 sum) ”
  &&  (intArray.full a_pre n_pre values)
) \/
(
forall (values : (List Int)) (n_pre : Int) (mn : Int) (sum : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values (0 : Int))) ∧ ((Znth k_2 values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= sum)) (PreH9 : (sum <= (100 * i))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 101)) (PreH12 : (PrefixSummary values i sum mn)) ,
  TT && emp 
|--
  “ (SearchMinimum values sum mn (0 : Int) 2 sum) ” &&
  “ (mn <= 100) ” &&
  “ (PrefixSummary values n_pre sum mn) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100))) ”
  &&  emp
)

noncomputable def solver_entail_wit_3_split_goal_1 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (mn : Int) (sum : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values (0 : Int))) ∧ ((Znth k_2 values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= sum)) (PreH9 : (sum <= (100 * i))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 101)) (PreH12 : (PrefixSummary values i sum mn)) ,
  (SearchMinimum values sum mn (0 : Int) 2 sum)

noncomputable def solver_entail_wit_3_split_goal_2 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (mn : Int) (sum : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values (0 : Int))) ∧ ((Znth k_2 values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= sum)) (PreH9 : (sum <= (100 * i))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 101)) (PreH12 : (PrefixSummary values i sum mn)) ,
  (mn <= 100)

noncomputable def solver_entail_wit_3_split_goal_3 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (mn : Int) (sum : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values (0 : Int))) ∧ ((Znth k_2 values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= sum)) (PreH9 : (sum <= (100 * i))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 101)) (PreH12 : (PrefixSummary values i sum mn)) ,
  (PrefixSummary values n_pre sum mn)

noncomputable def solver_entail_wit_3_split_goal_4 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (mn : Int) (sum : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values (0 : Int))) ∧ ((Znth k_2 values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= sum)) (PreH9 : (sum <= (100 * i))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 101)) (PreH12 : (PrefixSummary values i sum mn)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))

noncomputable def solver_entail_wit_4 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (i < n_pre)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values (0 : Int))) ∧ ((Znth k_2 values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= answer)) (PreH14 : (answer <= sum)) (PreH15 : (SearchMinimum values sum mn i 2 answer)) ,
  (intArray.full a_pre n_pre values)
|--
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 50000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100))) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ (PrefixSummary values n_pre sum mn) ” &&
  “ ((0 : Int) <= sum) ” &&
  “ (sum <= (100 * n_pre)) ” &&
  “ (1 <= mn) ” &&
  “ (mn <= 100) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (2 <= 2) ” &&
  “ (2 <= ((Znth i values (0 : Int)) + 1)) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= sum) ” &&
  “ (SearchMinimum values sum mn i 2 answer) ”
  &&  (intArray.full a_pre n_pre values)
) \/
(
forall (values : (List Int)) (n_pre : Int) (answer : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (i < n_pre)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values (0 : Int))) ∧ ((Znth k_2 values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= answer)) (PreH14 : (answer <= sum)) (PreH15 : (SearchMinimum values sum mn i 2 answer)) ,
  TT && emp 
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100))) ”
  &&  emp
)

noncomputable def solver_entail_wit_4_split_goal_1 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (answer : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (i < n_pre)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values (0 : Int))) ∧ ((Znth k_2 values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= answer)) (PreH14 : (answer <= sum)) (PreH15 : (SearchMinimum values sum mn i 2 answer)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))

noncomputable def solver_entail_wit_5_1 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (((((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x)) + (mn * x)) < answer)) (PreH2 : (x <= (Znth i values (0 : Int)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (PrefixSummary values n_pre sum mn)) (PreH8 : ((0 : Int) <= sum)) (PreH9 : (sum <= (100 * n_pre))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 100)) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : (2 <= x)) (PreH15 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer <= sum)) (PreH18 : (SearchMinimum values sum mn i x answer)) (PreH19 : ((Z.rem (Znth i values (0 : Int)) x) = (0 : Int))) ,
  (intArray.full a_pre n_pre values)
|--
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 50000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100))) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ (PrefixSummary values n_pre sum mn) ” &&
  “ ((0 : Int) <= sum) ” &&
  “ (sum <= (100 * n_pre)) ” &&
  “ (1 <= mn) ” &&
  “ (mn <= 100) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (2 <= (x + 1)) ” &&
  “ ((x + 1) <= ((Znth i values (0 : Int)) + 1)) ” &&
  “ ((0 : Int) <= ((((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x)) + (mn * x))) ” &&
  “ (((((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x)) + (mn * x)) <= sum) ” &&
  “ (SearchMinimum values sum mn i (x + 1) ((((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x)) + (mn * x))) ”
  &&  (intArray.full a_pre n_pre values)
) \/
(
forall (values : (List Int)) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (((((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x)) + (mn * x)) < answer)) (PreH2 : (x <= (Znth i values (0 : Int)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (PrefixSummary values n_pre sum mn)) (PreH8 : ((0 : Int) <= sum)) (PreH9 : (sum <= (100 * n_pre))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 100)) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : (2 <= x)) (PreH15 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer <= sum)) (PreH18 : (SearchMinimum values sum mn i x answer)) (PreH19 : ((Z.rem (Znth i values (0 : Int)) x) = (0 : Int))) ,
  TT && emp 
|--
  “ (SearchMinimum values sum mn i (x + 1) ((((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x)) + (mn * x))) ” &&
  “ ((0 : Int) <= ((((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x)) + (mn * x))) ”
  &&  emp
)

noncomputable def solver_entail_wit_5_1_split_goal_1 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (((((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x)) + (mn * x)) < answer)) (PreH2 : (x <= (Znth i values (0 : Int)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (PrefixSummary values n_pre sum mn)) (PreH8 : ((0 : Int) <= sum)) (PreH9 : (sum <= (100 * n_pre))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 100)) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : (2 <= x)) (PreH15 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer <= sum)) (PreH18 : (SearchMinimum values sum mn i x answer)) (PreH19 : ((Z.rem (Znth i values (0 : Int)) x) = (0 : Int))) ,
  (SearchMinimum values sum mn i (x + 1) ((((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x)) + (mn * x)))

noncomputable def solver_entail_wit_5_1_split_goal_2 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (((((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x)) + (mn * x)) < answer)) (PreH2 : (x <= (Znth i values (0 : Int)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (PrefixSummary values n_pre sum mn)) (PreH8 : ((0 : Int) <= sum)) (PreH9 : (sum <= (100 * n_pre))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 100)) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : (2 <= x)) (PreH15 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer <= sum)) (PreH18 : (SearchMinimum values sum mn i x answer)) (PreH19 : ((Z.rem (Znth i values (0 : Int)) x) = (0 : Int))) ,
  ((0 : Int) <= ((((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x)) + (mn * x)))

noncomputable def solver_entail_wit_5_2 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (((((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x)) + (mn * x)) >= answer)) (PreH2 : (x <= (Znth i values (0 : Int)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (PrefixSummary values n_pre sum mn)) (PreH8 : ((0 : Int) <= sum)) (PreH9 : (sum <= (100 * n_pre))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 100)) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : (2 <= x)) (PreH15 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer <= sum)) (PreH18 : (SearchMinimum values sum mn i x answer)) (PreH19 : ((Z.rem (Znth i values (0 : Int)) x) = (0 : Int))) ,
  (intArray.full a_pre n_pre values)
|--
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 50000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100))) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ (PrefixSummary values n_pre sum mn) ” &&
  “ ((0 : Int) <= sum) ” &&
  “ (sum <= (100 * n_pre)) ” &&
  “ (1 <= mn) ” &&
  “ (mn <= 100) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (2 <= (x + 1)) ” &&
  “ ((x + 1) <= ((Znth i values (0 : Int)) + 1)) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= sum) ” &&
  “ (SearchMinimum values sum mn i (x + 1) answer) ”
  &&  (intArray.full a_pre n_pre values)
) \/
(
forall (values : (List Int)) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (((((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x)) + (mn * x)) >= answer)) (PreH2 : (x <= (Znth i values (0 : Int)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (PrefixSummary values n_pre sum mn)) (PreH8 : ((0 : Int) <= sum)) (PreH9 : (sum <= (100 * n_pre))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 100)) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : (2 <= x)) (PreH15 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer <= sum)) (PreH18 : (SearchMinimum values sum mn i x answer)) (PreH19 : ((Z.rem (Znth i values (0 : Int)) x) = (0 : Int))) ,
  TT && emp 
|--
  “ (SearchMinimum values sum mn i (x + 1) answer) ”
  &&  emp
)

noncomputable def solver_entail_wit_5_2_split_goal_1 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (((((sum - (Znth i values (0 : Int))) - mn) + (Z.quot (Znth i values (0 : Int)) x)) + (mn * x)) >= answer)) (PreH2 : (x <= (Znth i values (0 : Int)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (PrefixSummary values n_pre sum mn)) (PreH8 : ((0 : Int) <= sum)) (PreH9 : (sum <= (100 * n_pre))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 100)) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : (2 <= x)) (PreH15 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer <= sum)) (PreH18 : (SearchMinimum values sum mn i x answer)) (PreH19 : ((Z.rem (Znth i values (0 : Int)) x) = (0 : Int))) ,
  (SearchMinimum values sum mn i (x + 1) answer)

noncomputable def solver_entail_wit_5_3 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (x <= (Znth i values (0 : Int)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH15 : ((0 : Int) <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer)) (PreH18 : ((Z.rem (Znth i values (0 : Int)) x) ≠ (0 : Int))) ,
  (intArray.full a_pre n_pre values)
|--
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 50000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100))) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ (PrefixSummary values n_pre sum mn) ” &&
  “ ((0 : Int) <= sum) ” &&
  “ (sum <= (100 * n_pre)) ” &&
  “ (1 <= mn) ” &&
  “ (mn <= 100) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (2 <= (x + 1)) ” &&
  “ ((x + 1) <= ((Znth i values (0 : Int)) + 1)) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= sum) ” &&
  “ (SearchMinimum values sum mn i (x + 1) answer) ”
  &&  (intArray.full a_pre n_pre values)
) \/
(
forall (values : (List Int)) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (x <= (Znth i values (0 : Int)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH15 : ((0 : Int) <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer)) (PreH18 : ((Z.rem (Znth i values (0 : Int)) x) ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (SearchMinimum values sum mn i (x + 1) answer) ”
  &&  emp
)

noncomputable def solver_entail_wit_5_3_split_goal_1 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (x <= (Znth i values (0 : Int)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH15 : ((0 : Int) <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer)) (PreH18 : ((Z.rem (Znth i values (0 : Int)) x) ≠ (0 : Int))) ,
  (SearchMinimum values sum mn i (x + 1) answer)

noncomputable def solver_entail_wit_6 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (x > (Znth i values (0 : Int)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values (0 : Int))) ∧ ((Znth k_2 values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH15 : ((0 : Int) <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer)) ,
  (intArray.full a_pre n_pre values)
|--
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 50000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100))) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ (PrefixSummary values n_pre sum mn) ” &&
  “ ((0 : Int) <= sum) ” &&
  “ (sum <= (100 * n_pre)) ” &&
  “ (1 <= mn) ” &&
  “ (mn <= 100) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= sum) ” &&
  “ (SearchMinimum values sum mn (i + 1) 2 answer) ”
  &&  (intArray.full a_pre n_pre values)
) \/
(
forall (values : (List Int)) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (x > (Znth i values (0 : Int)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values (0 : Int))) ∧ ((Znth k_2 values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH15 : ((0 : Int) <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer)) ,
  TT && emp 
|--
  “ (SearchMinimum values sum mn (i + 1) 2 answer) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100))) ”
  &&  emp
)

noncomputable def solver_entail_wit_6_split_goal_1 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (x > (Znth i values (0 : Int)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values (0 : Int))) ∧ ((Znth k_2 values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH15 : ((0 : Int) <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer)) ,
  (SearchMinimum values sum mn (i + 1) 2 answer)

noncomputable def solver_entail_wit_6_split_goal_2 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (x > (Znth i values (0 : Int)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values (0 : Int))) ∧ ((Znth k_2 values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH15 : ((0 : Int) <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= answer)) (PreH14 : (answer <= sum)) (PreH15 : (SearchMinimum values sum mn i 2 answer)) ,
  (intArray.full a_pre n_pre values)
|--
  “ (Spec values answer) ”
  &&  (intArray.full a_pre n_pre values)
) \/
(
forall (values : (List Int)) (n_pre : Int) (answer : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= answer)) (PreH14 : (answer <= sum)) (PreH15 : (SearchMinimum values sum mn i 2 answer)) ,
  TT && emp 
|--
  “ (Spec values answer) ”
  &&  emp
)

noncomputable def solver_return_wit_1_split_goal_1 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (answer : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= answer)) (PreH14 : (answer <= sum)) (PreH15 : (SearchMinimum values sum mn i 2 answer)) ,
  (Spec values answer)

noncomputable def solver_partial_solve_wit_1 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (mn : Int) (sum : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= sum)) (PreH9 : (sum <= (100 * i))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 101)) (PreH12 : (PrefixSummary values i sum mn)) ,
  (intArray.full a_pre n_pre values)
|--
  “ (i < n_pre) ” &&
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 50000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100))) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= sum) ” &&
  “ (sum <= (100 * i)) ” &&
  “ (1 <= mn) ” &&
  “ (mn <= 101) ” &&
  “ (PrefixSummary values i sum mn) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i values (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre values)

noncomputable def solver_partial_solve_wit_2 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (mn : Int) (sum : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= sum)) (PreH9 : (sum <= (100 * i))) (PreH10 : (1 <= mn)) (PreH11 : (mn <= 101)) (PreH12 : (PrefixSummary values i sum mn)) ,
  (intArray.full a_pre n_pre values)
|--
  “ (i < n_pre) ” &&
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 50000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100))) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= sum) ” &&
  “ (sum <= (100 * i)) ” &&
  “ (1 <= mn) ” &&
  “ (mn <= 101) ” &&
  “ (PrefixSummary values i sum mn) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i values (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre values)

noncomputable def solver_partial_solve_wit_3 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (mn : Int) (sum : Int) (i : Int) (PreH1 : ((Znth i values (0 : Int)) < mn)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 50000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= sum)) (PreH10 : (sum <= (100 * i))) (PreH11 : (1 <= mn)) (PreH12 : (mn <= 101)) (PreH13 : (PrefixSummary values i sum mn)) ,
  (intArray.full a_pre n_pre values)
|--
  “ ((Znth i values (0 : Int)) < mn) ” &&
  “ (i < n_pre) ” &&
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 50000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100))) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= sum) ” &&
  “ (sum <= (100 * i)) ” &&
  “ (1 <= mn) ” &&
  “ (mn <= 101) ” &&
  “ (PrefixSummary values i sum mn) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i values (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre values)

noncomputable def solver_partial_solve_wit_4 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (2 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 50000)) (PreH3 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (PrefixSummary values n_pre sum mn)) (PreH6 : ((0 : Int) <= sum)) (PreH7 : (sum <= (100 * n_pre))) (PreH8 : (1 <= mn)) (PreH9 : (mn <= 100)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : (2 <= x)) (PreH13 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH14 : ((0 : Int) <= answer)) (PreH15 : (answer <= sum)) (PreH16 : (SearchMinimum values sum mn i x answer)) ,
  (intArray.full a_pre n_pre values)
|--
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 50000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100))) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ (PrefixSummary values n_pre sum mn) ” &&
  “ ((0 : Int) <= sum) ” &&
  “ (sum <= (100 * n_pre)) ” &&
  “ (1 <= mn) ” &&
  “ (mn <= 100) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (2 <= x) ” &&
  “ (x <= ((Znth i values (0 : Int)) + 1)) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= sum) ” &&
  “ (SearchMinimum values sum mn i x answer) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i values (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre values)

noncomputable def solver_partial_solve_wit_5 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (x <= (Znth i values (0 : Int)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH15 : ((0 : Int) <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer)) ,
  (intArray.full a_pre n_pre values)
|--
  “ (x <= (Znth i values (0 : Int))) ” &&
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 50000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100))) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ (PrefixSummary values n_pre sum mn) ” &&
  “ ((0 : Int) <= sum) ” &&
  “ (sum <= (100 * n_pre)) ” &&
  “ (1 <= mn) ” &&
  “ (mn <= 100) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (2 <= x) ” &&
  “ (x <= ((Znth i values (0 : Int)) + 1)) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= sum) ” &&
  “ (SearchMinimum values sum mn i x answer) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i values (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre values)

noncomputable def solver_partial_solve_wit_6 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (x <= (Znth i values (0 : Int)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH15 : ((0 : Int) <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer)) (PreH18 : ((Z.rem (Znth i values (0 : Int)) x) = (0 : Int))) ,
  (intArray.full a_pre n_pre values)
|--
  “ (x <= (Znth i values (0 : Int))) ” &&
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 50000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100))) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ (PrefixSummary values n_pre sum mn) ” &&
  “ ((0 : Int) <= sum) ” &&
  “ (sum <= (100 * n_pre)) ” &&
  “ (1 <= mn) ” &&
  “ (mn <= 100) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (2 <= x) ” &&
  “ (x <= ((Znth i values (0 : Int)) + 1)) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= sum) ” &&
  “ (SearchMinimum values sum mn i x answer) ” &&
  “ ((Z.rem (Znth i values (0 : Int)) x) = (0 : Int)) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i values (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre values)

noncomputable def solver_partial_solve_wit_7 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (answer : Int) (x : Int) (i : Int) (sum : Int) (mn : Int) (PreH1 : (x <= (Znth i values (0 : Int)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 50000)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100)))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (PrefixSummary values n_pre sum mn)) (PreH7 : ((0 : Int) <= sum)) (PreH8 : (sum <= (100 * n_pre))) (PreH9 : (1 <= mn)) (PreH10 : (mn <= 100)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : (2 <= x)) (PreH14 : (x <= ((Znth i values (0 : Int)) + 1))) (PreH15 : ((0 : Int) <= answer)) (PreH16 : (answer <= sum)) (PreH17 : (SearchMinimum values sum mn i x answer)) (PreH18 : ((Z.rem (Znth i values (0 : Int)) x) = (0 : Int))) ,
  (intArray.full a_pre n_pre values)
|--
  “ (x <= (Znth i values (0 : Int))) ” &&
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 50000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= 100))) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ (PrefixSummary values n_pre sum mn) ” &&
  “ ((0 : Int) <= sum) ” &&
  “ (sum <= (100 * n_pre)) ” &&
  “ (1 <= mn) ” &&
  “ (mn <= 100) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (2 <= x) ” &&
  “ (x <= ((Znth i values (0 : Int)) + 1)) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= sum) ” &&
  “ (SearchMinimum values sum mn i x answer) ” &&
  “ ((Z.rem (Znth i values (0 : Int)) x) = (0 : Int)) ”
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
  proof_of_solver_safety_wit_13 : solver_safety_wit_13
  proof_of_solver_safety_wit_14 : solver_safety_wit_14
  proof_of_solver_safety_wit_15 : solver_safety_wit_15
  proof_of_solver_safety_wit_19 : solver_safety_wit_19
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2
  proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3
  proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4
  proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5
  proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6
  proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7
  proof_of_solver_safety_wit_10 : solver_safety_wit_10
  proof_of_solver_safety_wit_11 : solver_safety_wit_11
  proof_of_solver_safety_wit_12 : solver_safety_wit_12
  proof_of_solver_safety_wit_16 : solver_safety_wit_16
  proof_of_solver_safety_wit_17 : solver_safety_wit_17
  proof_of_solver_safety_wit_18 : solver_safety_wit_18
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1
  proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2
  proof_of_solver_entail_wit_3 : solver_entail_wit_3
  proof_of_solver_entail_wit_4 : solver_entail_wit_4
  proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1
  proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2
  proof_of_solver_entail_wit_5_3 : solver_entail_wit_5_3
  proof_of_solver_entail_wit_6 : solver_entail_wit_6
  proof_of_solver_return_wit_1 : solver_return_wit_1

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P030_1113B_sasha_and_magnetic_machines_goal
