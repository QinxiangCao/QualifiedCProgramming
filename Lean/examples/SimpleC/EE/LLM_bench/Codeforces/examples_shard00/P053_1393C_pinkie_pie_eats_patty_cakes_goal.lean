import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P053_1393C_pinkie_pie_eats_patty_cakes_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (PreH1 : (2 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 100000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> ((1 <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= (Zlength (values)))))) (PreH4 : (Pre values)) (PreH5 : (n_pre = (Zlength (values)))) ,
  ((( &( "cnt" ) )) # Ptr |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre values)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 100000)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> ((1 <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= (Zlength (values)))))) (PreH5 : (Pre values)) (PreH6 : (n_pre = (Zlength (values)))) ,
  ((( &( "mx" ) )) # Int |->_)
  ** (intArray.full retval (n_pre + 1) (repeat_Z ((0 : Int)) ((n_pre + 1))))
  ** ((( &( "cnt" ) )) # Ptr |-> (retval))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre values)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 100000)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> ((1 <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= (Zlength (values)))))) (PreH5 : (Pre values)) (PreH6 : (n_pre = (Zlength (values)))) ,
  ((( &( "c" ) )) # Int |->_)
  ** ((( &( "mx" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full retval (n_pre + 1) (repeat_Z ((0 : Int)) ((n_pre + 1))))
  ** ((( &( "cnt" ) )) # Ptr |-> (retval))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre values)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 100000)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> ((1 <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= (Zlength (values)))))) (PreH5 : (Pre values)) (PreH6 : (n_pre = (Zlength (values)))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "c" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "mx" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full retval (n_pre + 1) (repeat_Z ((0 : Int)) ((n_pre + 1))))
  ** ((( &( "cnt" ) )) # Ptr |-> (retval))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre values)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (counts : (List Int)) (i : Int) (c : Int) (mx : Int) (cnt : Int) (PreH1 : (i < n_pre)) (PreH2 : (cnt ≠ (0 : Int))) (PreH3 : (mx = (0 : Int))) (PreH4 : (c = (0 : Int))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH9 : (Pre values)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (CountPrefix values i counts)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= i)))) ,
  (intArray.full cnt (n_pre + 1) counts)
  ** (intArray.full a_pre n_pre values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "cnt" ) )) # Ptr |-> (cnt))
  ** ((( &( "mx" ) )) # Int |-> (mx))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "i" ) )) # Int |-> (i))
|--
  “ (((Znth (Znth i values (0 : Int)) counts (0 : Int)) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth (Znth i values (0 : Int)) counts (0 : Int)) + 1)) ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (counts : (List Int)) (i : Int) (c : Int) (mx : Int) (cnt : Int) (PreH1 : (i < n_pre)) (PreH2 : (cnt ≠ (0 : Int))) (PreH3 : (mx = (0 : Int))) (PreH4 : (c = (0 : Int))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH9 : (Pre values)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (CountPrefix values i counts)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= i)))) ,
  (intArray.full cnt (n_pre + 1) (replace_Znth ((Znth i values (0 : Int))) (((Znth (Znth i values (0 : Int)) counts (0 : Int)) + 1)) (counts)))
  ** (intArray.full a_pre n_pre values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "cnt" ) )) # Ptr |-> (cnt))
  ** ((( &( "mx" ) )) # Int |-> (mx))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "i" ) )) # Int |-> (i))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_7 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (counts : (List Int)) (i : Int) (c : Int) (mx : Int) (cnt : Int) (PreH1 : (i >= n_pre)) (PreH2 : (cnt ≠ (0 : Int))) (PreH3 : (mx = (0 : Int))) (PreH4 : (c = (0 : Int))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH9 : (Pre values)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (CountPrefix values i counts)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= i)))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "cnt" ) )) # Ptr |-> (cnt))
  ** ((( &( "mx" ) )) # Int |-> (mx))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** (intArray.full a_pre n_pre values)
  ** (intArray.full cnt (n_pre + 1) counts)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_8 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (counts : (List Int)) (c : Int) (mx : Int) (i : Int) (cnt : Int) (PreH1 : ((Znth i counts (0 : Int)) > mx)) (PreH2 : (i <= n_pre)) (PreH3 : (cnt ≠ (0 : Int))) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH8 : (Pre values)) (PreH9 : (1 <= i)) (PreH10 : (i <= (n_pre + 1))) (PreH11 : ((0 : Int) <= mx)) (PreH12 : (mx <= n_pre)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= (i - 1))) (PreH15 : (CountPrefix values n_pre counts)) (PreH16 : (MaximumFrequencyPrefix counts i mx c)) (PreH17 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= n_pre)))) ,
  (intArray.full cnt (n_pre + 1) counts)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "cnt" ) )) # Ptr |-> (cnt))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "mx" ) )) # Int |-> ((Znth i counts (0 : Int))))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** (intArray.full a_pre n_pre values)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_9 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (counts : (List Int)) (c : Int) (mx : Int) (i : Int) (cnt : Int) (PreH1 : ((Znth i counts (0 : Int)) = mx)) (PreH2 : ((Znth i counts (0 : Int)) <= mx)) (PreH3 : (i <= n_pre)) (PreH4 : (cnt ≠ (0 : Int))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH9 : (Pre values)) (PreH10 : (1 <= i)) (PreH11 : (i <= (n_pre + 1))) (PreH12 : ((0 : Int) <= mx)) (PreH13 : (mx <= n_pre)) (PreH14 : ((0 : Int) <= c)) (PreH15 : (c <= (i - 1))) (PreH16 : (CountPrefix values n_pre counts)) (PreH17 : (MaximumFrequencyPrefix counts i mx c)) (PreH18 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= n_pre)))) ,
  (intArray.full cnt (n_pre + 1) counts)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "cnt" ) )) # Ptr |-> (cnt))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "mx" ) )) # Int |-> (mx))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** (intArray.full a_pre n_pre values)
|--
  “ ((c + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (c + 1)) ”

noncomputable def solver_safety_wit_10 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (counts : (List Int)) (c : Int) (mx : Int) (i : Int) (cnt : Int) (PreH1 : ((Znth i counts (0 : Int)) > mx)) (PreH2 : (i <= n_pre)) (PreH3 : (cnt ≠ (0 : Int))) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH8 : (Pre values)) (PreH9 : (1 <= i)) (PreH10 : (i <= (n_pre + 1))) (PreH11 : ((0 : Int) <= mx)) (PreH12 : (mx <= n_pre)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= (i - 1))) (PreH15 : (CountPrefix values n_pre counts)) (PreH16 : (MaximumFrequencyPrefix counts i mx c)) (PreH17 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= n_pre)))) ,
  (intArray.full cnt (n_pre + 1) counts)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "cnt" ) )) # Ptr |-> (cnt))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "mx" ) )) # Int |-> ((Znth i counts (0 : Int))))
  ** ((( &( "c" ) )) # Int |-> (1))
  ** (intArray.full a_pre n_pre values)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_11 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (counts : (List Int)) (c : Int) (mx : Int) (i : Int) (cnt : Int) (PreH1 : ((Znth i counts (0 : Int)) = mx)) (PreH2 : ((Znth i counts (0 : Int)) <= mx)) (PreH3 : (i <= n_pre)) (PreH4 : (cnt ≠ (0 : Int))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH9 : (Pre values)) (PreH10 : (1 <= i)) (PreH11 : (i <= (n_pre + 1))) (PreH12 : ((0 : Int) <= mx)) (PreH13 : (mx <= n_pre)) (PreH14 : ((0 : Int) <= c)) (PreH15 : (c <= (i - 1))) (PreH16 : (CountPrefix values n_pre counts)) (PreH17 : (MaximumFrequencyPrefix counts i mx c)) (PreH18 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= n_pre)))) ,
  (intArray.full cnt (n_pre + 1) counts)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "cnt" ) )) # Ptr |-> (cnt))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "mx" ) )) # Int |-> (mx))
  ** ((( &( "c" ) )) # Int |-> ((c + 1)))
  ** (intArray.full a_pre n_pre values)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_12 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (counts : (List Int)) (c : Int) (mx : Int) (i : Int) (cnt : Int) (PreH1 : ((Znth i counts (0 : Int)) ≠ mx)) (PreH2 : ((Znth i counts (0 : Int)) <= mx)) (PreH3 : (i <= n_pre)) (PreH4 : (cnt ≠ (0 : Int))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH9 : (Pre values)) (PreH10 : (1 <= i)) (PreH11 : (i <= (n_pre + 1))) (PreH12 : ((0 : Int) <= mx)) (PreH13 : (mx <= n_pre)) (PreH14 : ((0 : Int) <= c)) (PreH15 : (c <= (i - 1))) (PreH16 : (CountPrefix values n_pre counts)) (PreH17 : (MaximumFrequencyPrefix counts i mx c)) (PreH18 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= n_pre)))) ,
  (intArray.full cnt (n_pre + 1) counts)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "cnt" ) )) # Ptr |-> (cnt))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "mx" ) )) # Int |-> (mx))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** (intArray.full a_pre n_pre values)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_13 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (counts : (List Int)) (c : Int) (mx : Int) (i : Int) (cnt : Int) (PreH1 : (i > n_pre)) (PreH2 : (cnt ≠ (0 : Int))) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH7 : (Pre values)) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1))) (PreH10 : ((0 : Int) <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : ((0 : Int) <= c)) (PreH13 : (c <= (i - 1))) (PreH14 : (CountPrefix values n_pre counts)) (PreH15 : (MaximumFrequencyPrefix counts i mx c)) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= n_pre)))) ,
  ((( &( "ans" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "cnt" ) )) # Ptr |-> (cnt))
  ** ((( &( "mx" ) )) # Int |-> (mx))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** (intArray.full a_pre n_pre values)
  ** (intArray.full cnt (n_pre + 1) counts)
|--
  “ (((Z.quot (n_pre - c) (mx - 1)) - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Z.quot (n_pre - c) (mx - 1)) - 1)) ”
) \/
(
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (counts : (List Int)) (c : Int) (mx : Int) (i : Int) (cnt : Int) (PreH1 : (i > n_pre)) (PreH2 : (cnt ≠ (0 : Int))) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH7 : (Pre values)) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1))) (PreH10 : ((0 : Int) <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : ((0 : Int) <= c)) (PreH13 : (c <= (i - 1))) (PreH14 : (CountPrefix values n_pre counts)) (PreH15 : (MaximumFrequencyPrefix counts i mx c)) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= n_pre)))) ,
  ((( &( "ans" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "cnt" ) )) # Ptr |-> (cnt))
  ** ((( &( "mx" ) )) # Int |-> (mx))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** (intArray.full a_pre n_pre values)
  ** (intArray.full cnt (n_pre + 1) counts)
|--
  “ (((Z.quot (n_pre - c) (mx - 1)) - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Z.quot (n_pre - c) (mx - 1)) - 1)) ”
)

noncomputable def solver_safety_wit_13_split_goal_1 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (counts : (List Int)) (c : Int) (mx : Int) (i : Int) (cnt : Int) (PreH1 : (i > n_pre)) (PreH2 : (cnt ≠ (0 : Int))) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH7 : (Pre values)) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1))) (PreH10 : ((0 : Int) <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : ((0 : Int) <= c)) (PreH13 : (c <= (i - 1))) (PreH14 : (CountPrefix values n_pre counts)) (PreH15 : (MaximumFrequencyPrefix counts i mx c)) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= n_pre)))) ,
  ((( &( "ans" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "cnt" ) )) # Ptr |-> (cnt))
  ** ((( &( "mx" ) )) # Int |-> (mx))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** (intArray.full a_pre n_pre values)
  ** (intArray.full cnt (n_pre + 1) counts)
|--
  “ (((Z.quot (n_pre - c) (mx - 1)) - 1) <= INT_MAX) ”

noncomputable def solver_safety_wit_13_split_goal_2 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (counts : (List Int)) (c : Int) (mx : Int) (i : Int) (cnt : Int) (PreH1 : (i > n_pre)) (PreH2 : (cnt ≠ (0 : Int))) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH7 : (Pre values)) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1))) (PreH10 : ((0 : Int) <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : ((0 : Int) <= c)) (PreH13 : (c <= (i - 1))) (PreH14 : (CountPrefix values n_pre counts)) (PreH15 : (MaximumFrequencyPrefix counts i mx c)) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= n_pre)))) ,
  ((( &( "ans" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "cnt" ) )) # Ptr |-> (cnt))
  ** ((( &( "mx" ) )) # Int |-> (mx))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** (intArray.full a_pre n_pre values)
  ** (intArray.full cnt (n_pre + 1) counts)
|--
  “ ((INT_MIN) <= ((Z.quot (n_pre - c) (mx - 1)) - 1)) ”

noncomputable def solver_safety_wit_14 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (counts : (List Int)) (c : Int) (mx : Int) (i : Int) (cnt : Int) (PreH1 : (i > n_pre)) (PreH2 : (cnt ≠ (0 : Int))) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH7 : (Pre values)) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1))) (PreH10 : ((0 : Int) <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : ((0 : Int) <= c)) (PreH13 : (c <= (i - 1))) (PreH14 : (CountPrefix values n_pre counts)) (PreH15 : (MaximumFrequencyPrefix counts i mx c)) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= n_pre)))) ,
  ((( &( "ans" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "cnt" ) )) # Ptr |-> (cnt))
  ** ((( &( "mx" ) )) # Int |-> (mx))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** (intArray.full a_pre n_pre values)
  ** (intArray.full cnt (n_pre + 1) counts)
|--
  “ (((n_pre - c) ≠ (INT_MIN)) ∨ ((mx - 1) ≠ (-1))) ” &&
  “ ((mx - 1) ≠ (0 : Int)) ”
) \/
(
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (counts : (List Int)) (c : Int) (mx : Int) (i : Int) (cnt : Int) (PreH1 : (i > n_pre)) (PreH2 : (cnt ≠ (0 : Int))) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH7 : (Pre values)) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1))) (PreH10 : ((0 : Int) <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : ((0 : Int) <= c)) (PreH13 : (c <= (i - 1))) (PreH14 : (CountPrefix values n_pre counts)) (PreH15 : (MaximumFrequencyPrefix counts i mx c)) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= n_pre)))) ,
  ((( &( "ans" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "cnt" ) )) # Ptr |-> (cnt))
  ** ((( &( "mx" ) )) # Int |-> (mx))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** (intArray.full a_pre n_pre values)
  ** (intArray.full cnt (n_pre + 1) counts)
|--
  “ (((n_pre - c) ≠ (INT_MIN)) ∨ ((mx - 1) ≠ (-1))) ” &&
  “ ((mx - 1) ≠ (0 : Int)) ”
)

noncomputable def solver_safety_wit_14_split_goal_1 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (counts : (List Int)) (c : Int) (mx : Int) (i : Int) (cnt : Int) (PreH1 : (i > n_pre)) (PreH2 : (cnt ≠ (0 : Int))) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH7 : (Pre values)) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1))) (PreH10 : ((0 : Int) <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : ((0 : Int) <= c)) (PreH13 : (c <= (i - 1))) (PreH14 : (CountPrefix values n_pre counts)) (PreH15 : (MaximumFrequencyPrefix counts i mx c)) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= n_pre)))) ,
  ((( &( "ans" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "cnt" ) )) # Ptr |-> (cnt))
  ** ((( &( "mx" ) )) # Int |-> (mx))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** (intArray.full a_pre n_pre values)
  ** (intArray.full cnt (n_pre + 1) counts)
|--
  “ (((n_pre - c) ≠ (INT_MIN)) ∨ ((mx - 1) ≠ (-1))) ”

noncomputable def solver_safety_wit_14_split_goal_2 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (counts : (List Int)) (c : Int) (mx : Int) (i : Int) (cnt : Int) (PreH1 : (i > n_pre)) (PreH2 : (cnt ≠ (0 : Int))) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH7 : (Pre values)) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1))) (PreH10 : ((0 : Int) <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : ((0 : Int) <= c)) (PreH13 : (c <= (i - 1))) (PreH14 : (CountPrefix values n_pre counts)) (PreH15 : (MaximumFrequencyPrefix counts i mx c)) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= n_pre)))) ,
  ((( &( "ans" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "cnt" ) )) # Ptr |-> (cnt))
  ** ((( &( "mx" ) )) # Int |-> (mx))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** (intArray.full a_pre n_pre values)
  ** (intArray.full cnt (n_pre + 1) counts)
|--
  “ ((mx - 1) ≠ (0 : Int)) ”

noncomputable def solver_safety_wit_15 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (counts : (List Int)) (c : Int) (mx : Int) (i : Int) (cnt : Int) (PreH1 : (i > n_pre)) (PreH2 : (cnt ≠ (0 : Int))) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH7 : (Pre values)) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1))) (PreH10 : ((0 : Int) <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : ((0 : Int) <= c)) (PreH13 : (c <= (i - 1))) (PreH14 : (CountPrefix values n_pre counts)) (PreH15 : (MaximumFrequencyPrefix counts i mx c)) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= n_pre)))) ,
  ((( &( "ans" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "cnt" ) )) # Ptr |-> (cnt))
  ** ((( &( "mx" ) )) # Int |-> (mx))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** (intArray.full a_pre n_pre values)
  ** (intArray.full cnt (n_pre + 1) counts)
|--
  “ ((mx - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (mx - 1)) ”

noncomputable def solver_safety_wit_16 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (counts : (List Int)) (c : Int) (mx : Int) (i : Int) (cnt : Int) (PreH1 : (i > n_pre)) (PreH2 : (cnt ≠ (0 : Int))) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH7 : (Pre values)) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1))) (PreH10 : ((0 : Int) <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : ((0 : Int) <= c)) (PreH13 : (c <= (i - 1))) (PreH14 : (CountPrefix values n_pre counts)) (PreH15 : (MaximumFrequencyPrefix counts i mx c)) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= n_pre)))) ,
  ((( &( "ans" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "cnt" ) )) # Ptr |-> (cnt))
  ** ((( &( "mx" ) )) # Int |-> (mx))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** (intArray.full a_pre n_pre values)
  ** (intArray.full cnt (n_pre + 1) counts)
|--
  “ ((n_pre - c) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre - c)) ”

noncomputable def solver_safety_wit_17 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (counts : (List Int)) (c : Int) (mx : Int) (i : Int) (cnt : Int) (PreH1 : (i > n_pre)) (PreH2 : (cnt ≠ (0 : Int))) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH7 : (Pre values)) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1))) (PreH10 : ((0 : Int) <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : ((0 : Int) <= c)) (PreH13 : (c <= (i - 1))) (PreH14 : (CountPrefix values n_pre counts)) (PreH15 : (MaximumFrequencyPrefix counts i mx c)) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= n_pre)))) ,
  ((( &( "ans" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "cnt" ) )) # Ptr |-> (cnt))
  ** ((( &( "mx" ) )) # Int |-> (mx))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** (intArray.full a_pre n_pre values)
  ** (intArray.full cnt (n_pre + 1) counts)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_18 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (counts : (List Int)) (c : Int) (mx : Int) (i : Int) (cnt : Int) (PreH1 : (i > n_pre)) (PreH2 : (cnt ≠ (0 : Int))) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH7 : (Pre values)) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1))) (PreH10 : ((0 : Int) <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : ((0 : Int) <= c)) (PreH13 : (c <= (i - 1))) (PreH14 : (CountPrefix values n_pre counts)) (PreH15 : (MaximumFrequencyPrefix counts i mx c)) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= n_pre)))) ,
  ((( &( "ans" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "cnt" ) )) # Ptr |-> (cnt))
  ** ((( &( "mx" ) )) # Int |-> (mx))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** (intArray.full a_pre n_pre values)
  ** (intArray.full cnt (n_pre + 1) counts)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 100000)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> ((1 <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= (Zlength (values)))))) (PreH5 : (Pre values)) (PreH6 : (n_pre = (Zlength (values)))) ,
  (intArray.full retval (n_pre + 1) (repeat_Z ((0 : Int)) ((n_pre + 1))))
  ** (intArray.full a_pre n_pre values)
|--
  EX counts : (List Int),
  “ (retval ≠ (0 : Int)) ” &&
  “ ((0 : Int) = (0 : Int)) ” &&
  “ ((0 : Int) = (0 : Int)) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values))))) ” &&
  “ (Pre values) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (CountPrefix values (0 : Int) counts) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= (0 : Int)))) ”
  &&  (intArray.full a_pre n_pre values)
  ** (intArray.full retval (n_pre + 1) counts)
) \/
(
forall (values : (List Int)) (n_pre : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 100000)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> ((1 <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= (Zlength (values)))))) (PreH5 : (Pre values)) (PreH6 : (n_pre = (Zlength (values)))) ,
  TT && emp 
|--
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 (repeat_Z ((0 : Int)) ((n_pre + 1))) (0 : Int))) ∧ ((Znth k_2 (repeat_Z ((0 : Int)) ((n_pre + 1))) (0 : Int)) <= (0 : Int)))) ” &&
  “ (CountPrefix values (0 : Int) (repeat_Z ((0 : Int)) ((n_pre + 1)))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values))))) ”
  &&  emp
)

noncomputable def solver_entail_wit_1_split_goal_1 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 100000)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> ((1 <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= (Zlength (values)))))) (PreH5 : (Pre values)) (PreH6 : (n_pre = (Zlength (values)))) ,
  forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 (repeat_Z ((0 : Int)) ((n_pre + 1))) (0 : Int))) ∧ ((Znth k_2 (repeat_Z ((0 : Int)) ((n_pre + 1))) (0 : Int)) <= (0 : Int))))

noncomputable def solver_entail_wit_1_split_goal_2 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 100000)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> ((1 <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= (Zlength (values)))))) (PreH5 : (Pre values)) (PreH6 : (n_pre = (Zlength (values)))) ,
  (CountPrefix values (0 : Int) (repeat_Z ((0 : Int)) ((n_pre + 1))))

noncomputable def solver_entail_wit_1_split_goal_3 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 100000)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> ((1 <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= (Zlength (values)))))) (PreH5 : (Pre values)) (PreH6 : (n_pre = (Zlength (values)))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))

noncomputable def solver_entail_wit_2 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (counts_2 : (List Int)) (i : Int) (c : Int) (mx : Int) (cnt : Int) (PreH1 : (i < n_pre)) (PreH2 : (cnt ≠ (0 : Int))) (PreH3 : (mx = (0 : Int))) (PreH4 : (c = (0 : Int))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH9 : (Pre values)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (CountPrefix values i counts_2)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts_2 (0 : Int))) ∧ ((Znth k_2 counts_2 (0 : Int)) <= i)))) ,
  (intArray.full cnt (n_pre + 1) (replace_Znth ((Znth i values (0 : Int))) (((Znth (Znth i values (0 : Int)) counts_2 (0 : Int)) + 1)) (counts_2)))
  ** (intArray.full a_pre n_pre values)
|--
  EX counts : (List Int),
  “ (cnt ≠ (0 : Int)) ” &&
  “ (mx = (0 : Int)) ” &&
  “ (c = (0 : Int)) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values))))) ” &&
  “ (Pre values) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ (CountPrefix values (i + 1) counts) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= (i + 1)))) ”
  &&  (intArray.full a_pre n_pre values)
  ** (intArray.full cnt (n_pre + 1) counts)
) \/
(
forall (values : (List Int)) (n_pre : Int) (counts_2 : (List Int)) (i : Int) (c : Int) (mx : Int) (cnt : Int) (PreH1 : (i < n_pre)) (PreH2 : (cnt ≠ (0 : Int))) (PreH3 : (mx = (0 : Int))) (PreH4 : (c = (0 : Int))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH9 : (Pre values)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (CountPrefix values i counts_2)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts_2 (0 : Int))) ∧ ((Znth k_2 counts_2 (0 : Int)) <= i)))) ,
  TT && emp 
|--
  “ (CountPrefix values (i + 1) (replace_Znth ((Znth i values (0 : Int))) (((Znth (Znth i values (0 : Int)) counts_2 (0 : Int)) + 1)) (counts_2))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_split_goal_1 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (counts_2 : (List Int)) (i : Int) (c : Int) (mx : Int) (cnt : Int) (PreH1 : (i < n_pre)) (PreH2 : (cnt ≠ (0 : Int))) (PreH3 : (mx = (0 : Int))) (PreH4 : (c = (0 : Int))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH9 : (Pre values)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (CountPrefix values i counts_2)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts_2 (0 : Int))) ∧ ((Znth k_2 counts_2 (0 : Int)) <= i)))) ,
  (CountPrefix values (i + 1) (replace_Znth ((Znth i values (0 : Int))) (((Znth (Znth i values (0 : Int)) counts_2 (0 : Int)) + 1)) (counts_2)))

noncomputable def solver_entail_wit_3 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (counts_2 : (List Int)) (i : Int) (c : Int) (mx : Int) (cnt : Int) (PreH1 : (i >= n_pre)) (PreH2 : (cnt ≠ (0 : Int))) (PreH3 : (mx = (0 : Int))) (PreH4 : (c = (0 : Int))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= (Zlength (values)))))) (PreH9 : (Pre values)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (CountPrefix values i counts_2)) (PreH13 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 <= n_pre)) -> (((0 : Int) <= (Znth k_4 counts_2 (0 : Int))) ∧ ((Znth k_4 counts_2 (0 : Int)) <= i)))) ,
  (intArray.full a_pre n_pre values)
  ** (intArray.full cnt (n_pre + 1) counts_2)
|--
  EX counts : (List Int),
  “ (cnt ≠ (0 : Int)) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values))))) ” &&
  “ (Pre values) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= mx) ” &&
  “ (mx <= n_pre) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= (1 - 1)) ” &&
  “ (CountPrefix values n_pre counts) ” &&
  “ (MaximumFrequencyPrefix counts 1 mx c) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= n_pre))) ”
  &&  (intArray.full a_pre n_pre values)
  ** (intArray.full cnt (n_pre + 1) counts)
) \/
(
forall (values : (List Int)) (n_pre : Int) (counts_2 : (List Int)) (i : Int) (c : Int) (mx : Int) (cnt : Int) (PreH1 : (i >= n_pre)) (PreH2 : (cnt ≠ (0 : Int))) (PreH3 : (mx = (0 : Int))) (PreH4 : (c = (0 : Int))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= (Zlength (values)))))) (PreH9 : (Pre values)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (CountPrefix values i counts_2)) (PreH13 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 <= n_pre)) -> (((0 : Int) <= (Znth k_4 counts_2 (0 : Int))) ∧ ((Znth k_4 counts_2 (0 : Int)) <= i)))) ,
  TT && emp 
|--
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts_2 (0 : Int))) ∧ ((Znth k_2 counts_2 (0 : Int)) <= n_pre))) ” &&
  “ (MaximumFrequencyPrefix counts_2 1 (0 : Int) (0 : Int)) ” &&
  “ (CountPrefix values n_pre counts_2) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values))))) ”
  &&  emp
)

noncomputable def solver_entail_wit_3_split_goal_1 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (counts_2 : (List Int)) (i : Int) (c : Int) (mx : Int) (cnt : Int) (PreH1 : (i >= n_pre)) (PreH2 : (cnt ≠ (0 : Int))) (PreH3 : (mx = (0 : Int))) (PreH4 : (c = (0 : Int))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= (Zlength (values)))))) (PreH9 : (Pre values)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (CountPrefix values i counts_2)) (PreH13 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 <= n_pre)) -> (((0 : Int) <= (Znth k_4 counts_2 (0 : Int))) ∧ ((Znth k_4 counts_2 (0 : Int)) <= i)))) ,
  forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts_2 (0 : Int))) ∧ ((Znth k_2 counts_2 (0 : Int)) <= n_pre)))

noncomputable def solver_entail_wit_3_split_goal_2 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (counts_2 : (List Int)) (i : Int) (c : Int) (mx : Int) (cnt : Int) (PreH1 : (i >= n_pre)) (PreH2 : (cnt ≠ (0 : Int))) (PreH3 : (mx = (0 : Int))) (PreH4 : (c = (0 : Int))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= (Zlength (values)))))) (PreH9 : (Pre values)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (CountPrefix values i counts_2)) (PreH13 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 <= n_pre)) -> (((0 : Int) <= (Znth k_4 counts_2 (0 : Int))) ∧ ((Znth k_4 counts_2 (0 : Int)) <= i)))) ,
  (MaximumFrequencyPrefix counts_2 1 (0 : Int) (0 : Int))

noncomputable def solver_entail_wit_3_split_goal_3 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (counts_2 : (List Int)) (i : Int) (c : Int) (mx : Int) (cnt : Int) (PreH1 : (i >= n_pre)) (PreH2 : (cnt ≠ (0 : Int))) (PreH3 : (mx = (0 : Int))) (PreH4 : (c = (0 : Int))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= (Zlength (values)))))) (PreH9 : (Pre values)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (CountPrefix values i counts_2)) (PreH13 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 <= n_pre)) -> (((0 : Int) <= (Znth k_4 counts_2 (0 : Int))) ∧ ((Znth k_4 counts_2 (0 : Int)) <= i)))) ,
  (CountPrefix values n_pre counts_2)

noncomputable def solver_entail_wit_3_split_goal_4 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (counts_2 : (List Int)) (i : Int) (c : Int) (mx : Int) (cnt : Int) (PreH1 : (i >= n_pre)) (PreH2 : (cnt ≠ (0 : Int))) (PreH3 : (mx = (0 : Int))) (PreH4 : (c = (0 : Int))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values (0 : Int))) ∧ ((Znth k_3 values (0 : Int)) <= (Zlength (values)))))) (PreH9 : (Pre values)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (CountPrefix values i counts_2)) (PreH13 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 <= n_pre)) -> (((0 : Int) <= (Znth k_4 counts_2 (0 : Int))) ∧ ((Znth k_4 counts_2 (0 : Int)) <= i)))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))

noncomputable def solver_entail_wit_4_1 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (counts_2 : (List Int)) (c : Int) (mx : Int) (i : Int) (cnt : Int) (PreH1 : ((Znth i counts_2 (0 : Int)) > mx)) (PreH2 : (i <= n_pre)) (PreH3 : (cnt ≠ (0 : Int))) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH8 : (Pre values)) (PreH9 : (1 <= i)) (PreH10 : (i <= (n_pre + 1))) (PreH11 : ((0 : Int) <= mx)) (PreH12 : (mx <= n_pre)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= (i - 1))) (PreH15 : (CountPrefix values n_pre counts_2)) (PreH16 : (MaximumFrequencyPrefix counts_2 i mx c)) (PreH17 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts_2 (0 : Int))) ∧ ((Znth k_2 counts_2 (0 : Int)) <= n_pre)))) ,
  (intArray.full cnt (n_pre + 1) counts_2)
  ** (intArray.full a_pre n_pre values)
|--
  EX counts : (List Int),
  “ (cnt ≠ (0 : Int)) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values))))) ” &&
  “ (Pre values) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= (Znth i counts_2 (0 : Int))) ” &&
  “ ((Znth i counts_2 (0 : Int)) <= n_pre) ” &&
  “ ((0 : Int) <= 1) ” &&
  “ (1 <= ((i + 1) - 1)) ” &&
  “ (CountPrefix values n_pre counts) ” &&
  “ (MaximumFrequencyPrefix counts (i + 1) (Znth i counts_2 (0 : Int)) 1) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= n_pre))) ”
  &&  (intArray.full a_pre n_pre values)
  ** (intArray.full cnt (n_pre + 1) counts)
) \/
(
forall (values : (List Int)) (n_pre : Int) (counts_2 : (List Int)) (c : Int) (mx : Int) (i : Int) (cnt : Int) (PreH1 : ((Znth i counts_2 (0 : Int)) > mx)) (PreH2 : (i <= n_pre)) (PreH3 : (cnt ≠ (0 : Int))) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH8 : (Pre values)) (PreH9 : (1 <= i)) (PreH10 : (i <= (n_pre + 1))) (PreH11 : ((0 : Int) <= mx)) (PreH12 : (mx <= n_pre)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= (i - 1))) (PreH15 : (CountPrefix values n_pre counts_2)) (PreH16 : (MaximumFrequencyPrefix counts_2 i mx c)) (PreH17 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts_2 (0 : Int))) ∧ ((Znth k_2 counts_2 (0 : Int)) <= n_pre)))) ,
  TT && emp 
|--
  “ (MaximumFrequencyPrefix counts_2 (i + 1) (Znth i counts_2 (0 : Int)) 1) ”
  &&  emp
)

noncomputable def solver_entail_wit_4_1_split_goal_1 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (counts_2 : (List Int)) (c : Int) (mx : Int) (i : Int) (cnt : Int) (PreH1 : ((Znth i counts_2 (0 : Int)) > mx)) (PreH2 : (i <= n_pre)) (PreH3 : (cnt ≠ (0 : Int))) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH8 : (Pre values)) (PreH9 : (1 <= i)) (PreH10 : (i <= (n_pre + 1))) (PreH11 : ((0 : Int) <= mx)) (PreH12 : (mx <= n_pre)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= (i - 1))) (PreH15 : (CountPrefix values n_pre counts_2)) (PreH16 : (MaximumFrequencyPrefix counts_2 i mx c)) (PreH17 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts_2 (0 : Int))) ∧ ((Znth k_2 counts_2 (0 : Int)) <= n_pre)))) ,
  (MaximumFrequencyPrefix counts_2 (i + 1) (Znth i counts_2 (0 : Int)) 1)

noncomputable def solver_entail_wit_4_2 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (counts_2 : (List Int)) (c : Int) (mx : Int) (i : Int) (cnt : Int) (PreH1 : ((Znth i counts_2 (0 : Int)) = mx)) (PreH2 : ((Znth i counts_2 (0 : Int)) <= mx)) (PreH3 : (i <= n_pre)) (PreH4 : (cnt ≠ (0 : Int))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH9 : (Pre values)) (PreH10 : (1 <= i)) (PreH11 : (i <= (n_pre + 1))) (PreH12 : ((0 : Int) <= mx)) (PreH13 : (mx <= n_pre)) (PreH14 : ((0 : Int) <= c)) (PreH15 : (c <= (i - 1))) (PreH16 : (CountPrefix values n_pre counts_2)) (PreH17 : (MaximumFrequencyPrefix counts_2 i mx c)) (PreH18 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts_2 (0 : Int))) ∧ ((Znth k_2 counts_2 (0 : Int)) <= n_pre)))) ,
  (intArray.full cnt (n_pre + 1) counts_2)
  ** (intArray.full a_pre n_pre values)
|--
  EX counts : (List Int),
  “ (cnt ≠ (0 : Int)) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values))))) ” &&
  “ (Pre values) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= mx) ” &&
  “ (mx <= n_pre) ” &&
  “ ((0 : Int) <= (c + 1)) ” &&
  “ ((c + 1) <= ((i + 1) - 1)) ” &&
  “ (CountPrefix values n_pre counts) ” &&
  “ (MaximumFrequencyPrefix counts (i + 1) mx (c + 1)) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= n_pre))) ”
  &&  (intArray.full a_pre n_pre values)
  ** (intArray.full cnt (n_pre + 1) counts)
) \/
(
forall (values : (List Int)) (n_pre : Int) (counts_2 : (List Int)) (c : Int) (mx : Int) (i : Int) (cnt : Int) (PreH1 : ((Znth i counts_2 (0 : Int)) = mx)) (PreH2 : ((Znth i counts_2 (0 : Int)) <= mx)) (PreH3 : (i <= n_pre)) (PreH4 : (cnt ≠ (0 : Int))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH9 : (Pre values)) (PreH10 : (1 <= i)) (PreH11 : (i <= (n_pre + 1))) (PreH12 : ((0 : Int) <= mx)) (PreH13 : (mx <= n_pre)) (PreH14 : ((0 : Int) <= c)) (PreH15 : (c <= (i - 1))) (PreH16 : (CountPrefix values n_pre counts_2)) (PreH17 : (MaximumFrequencyPrefix counts_2 i mx c)) (PreH18 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts_2 (0 : Int))) ∧ ((Znth k_2 counts_2 (0 : Int)) <= n_pre)))) ,
  TT && emp 
|--
  “ (MaximumFrequencyPrefix counts_2 (i + 1) mx (c + 1)) ”
  &&  emp
)

noncomputable def solver_entail_wit_4_2_split_goal_1 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (counts_2 : (List Int)) (c : Int) (mx : Int) (i : Int) (cnt : Int) (PreH1 : ((Znth i counts_2 (0 : Int)) = mx)) (PreH2 : ((Znth i counts_2 (0 : Int)) <= mx)) (PreH3 : (i <= n_pre)) (PreH4 : (cnt ≠ (0 : Int))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH9 : (Pre values)) (PreH10 : (1 <= i)) (PreH11 : (i <= (n_pre + 1))) (PreH12 : ((0 : Int) <= mx)) (PreH13 : (mx <= n_pre)) (PreH14 : ((0 : Int) <= c)) (PreH15 : (c <= (i - 1))) (PreH16 : (CountPrefix values n_pre counts_2)) (PreH17 : (MaximumFrequencyPrefix counts_2 i mx c)) (PreH18 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts_2 (0 : Int))) ∧ ((Znth k_2 counts_2 (0 : Int)) <= n_pre)))) ,
  (MaximumFrequencyPrefix counts_2 (i + 1) mx (c + 1))

noncomputable def solver_entail_wit_4_3 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (counts_2 : (List Int)) (c : Int) (mx : Int) (i : Int) (cnt : Int) (PreH1 : ((Znth i counts_2 (0 : Int)) ≠ mx)) (PreH2 : ((Znth i counts_2 (0 : Int)) <= mx)) (PreH3 : (i <= n_pre)) (PreH4 : (cnt ≠ (0 : Int))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH9 : (Pre values)) (PreH10 : (1 <= i)) (PreH11 : (i <= (n_pre + 1))) (PreH12 : ((0 : Int) <= mx)) (PreH13 : (mx <= n_pre)) (PreH14 : ((0 : Int) <= c)) (PreH15 : (c <= (i - 1))) (PreH16 : (CountPrefix values n_pre counts_2)) (PreH17 : (MaximumFrequencyPrefix counts_2 i mx c)) (PreH18 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts_2 (0 : Int))) ∧ ((Znth k_2 counts_2 (0 : Int)) <= n_pre)))) ,
  (intArray.full cnt (n_pre + 1) counts_2)
  ** (intArray.full a_pre n_pre values)
|--
  EX counts : (List Int),
  “ (cnt ≠ (0 : Int)) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values))))) ” &&
  “ (Pre values) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= mx) ” &&
  “ (mx <= n_pre) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= ((i + 1) - 1)) ” &&
  “ (CountPrefix values n_pre counts) ” &&
  “ (MaximumFrequencyPrefix counts (i + 1) mx c) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= n_pre))) ”
  &&  (intArray.full a_pre n_pre values)
  ** (intArray.full cnt (n_pre + 1) counts)
) \/
(
forall (values : (List Int)) (n_pre : Int) (counts_2 : (List Int)) (c : Int) (mx : Int) (i : Int) (cnt : Int) (PreH1 : ((Znth i counts_2 (0 : Int)) ≠ mx)) (PreH2 : ((Znth i counts_2 (0 : Int)) <= mx)) (PreH3 : (i <= n_pre)) (PreH4 : (cnt ≠ (0 : Int))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH9 : (Pre values)) (PreH10 : (1 <= i)) (PreH11 : (i <= (n_pre + 1))) (PreH12 : ((0 : Int) <= mx)) (PreH13 : (mx <= n_pre)) (PreH14 : ((0 : Int) <= c)) (PreH15 : (c <= (i - 1))) (PreH16 : (CountPrefix values n_pre counts_2)) (PreH17 : (MaximumFrequencyPrefix counts_2 i mx c)) (PreH18 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts_2 (0 : Int))) ∧ ((Znth k_2 counts_2 (0 : Int)) <= n_pre)))) ,
  TT && emp 
|--
  “ (MaximumFrequencyPrefix counts_2 (i + 1) mx c) ”
  &&  emp
)

noncomputable def solver_entail_wit_4_3_split_goal_1 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (counts_2 : (List Int)) (c : Int) (mx : Int) (i : Int) (cnt : Int) (PreH1 : ((Znth i counts_2 (0 : Int)) ≠ mx)) (PreH2 : ((Znth i counts_2 (0 : Int)) <= mx)) (PreH3 : (i <= n_pre)) (PreH4 : (cnt ≠ (0 : Int))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH9 : (Pre values)) (PreH10 : (1 <= i)) (PreH11 : (i <= (n_pre + 1))) (PreH12 : ((0 : Int) <= mx)) (PreH13 : (mx <= n_pre)) (PreH14 : ((0 : Int) <= c)) (PreH15 : (c <= (i - 1))) (PreH16 : (CountPrefix values n_pre counts_2)) (PreH17 : (MaximumFrequencyPrefix counts_2 i mx c)) (PreH18 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts_2 (0 : Int))) ∧ ((Znth k_2 counts_2 (0 : Int)) <= n_pre)))) ,
  (MaximumFrequencyPrefix counts_2 (i + 1) mx c)

noncomputable def solver_entail_wit_5 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (counts_2 : (List Int)) (c : Int) (mx : Int) (i : Int) (cnt : Int) (PreH1 : (i > n_pre)) (PreH2 : (cnt ≠ (0 : Int))) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values (0 : Int))) ∧ ((Znth k_2 values (0 : Int)) <= (Zlength (values)))))) (PreH7 : (Pre values)) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1))) (PreH10 : ((0 : Int) <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : ((0 : Int) <= c)) (PreH13 : (c <= (i - 1))) (PreH14 : (CountPrefix values n_pre counts_2)) (PreH15 : (MaximumFrequencyPrefix counts_2 i mx c)) (PreH16 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= n_pre)) -> (((0 : Int) <= (Znth k_3 counts_2 (0 : Int))) ∧ ((Znth k_3 counts_2 (0 : Int)) <= n_pre)))) ,
  (intArray.full a_pre n_pre values)
  ** (intArray.full cnt (n_pre + 1) counts_2)
|--
  EX counts : (List Int),
  “ (cnt ≠ (0 : Int)) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values))))) ” &&
  “ (Pre values) ” &&
  “ (2 <= mx) ” &&
  “ (mx <= n_pre) ” &&
  “ (1 <= c) ” &&
  “ (c <= n_pre) ” &&
  “ (((Z.quot (n_pre - c) (mx - 1)) - 1) = ((Z.quot (n_pre - c) (mx - 1)) - 1)) ” &&
  “ (CountPrefix values n_pre counts) ” &&
  “ (MaximumFrequencyPrefix counts (n_pre + 1) mx c) ” &&
  “ (Spec values ((Z.quot (n_pre - c) (mx - 1)) - 1)) ”
  &&  (intArray.full a_pre n_pre values)
  ** (intArray.full cnt (n_pre + 1) counts)
) \/
(
forall (values : (List Int)) (n_pre : Int) (counts_2 : (List Int)) (c : Int) (mx : Int) (i : Int) (cnt : Int) (PreH1 : (i > n_pre)) (PreH2 : (cnt ≠ (0 : Int))) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values (0 : Int))) ∧ ((Znth k_2 values (0 : Int)) <= (Zlength (values)))))) (PreH7 : (Pre values)) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1))) (PreH10 : ((0 : Int) <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : ((0 : Int) <= c)) (PreH13 : (c <= (i - 1))) (PreH14 : (CountPrefix values n_pre counts_2)) (PreH15 : (MaximumFrequencyPrefix counts_2 i mx c)) (PreH16 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= n_pre)) -> (((0 : Int) <= (Znth k_3 counts_2 (0 : Int))) ∧ ((Znth k_3 counts_2 (0 : Int)) <= n_pre)))) ,
  TT && emp 
|--
  “ (Spec values ((Z.quot (n_pre - c) (mx - 1)) - 1)) ” &&
  “ (MaximumFrequencyPrefix counts_2 (n_pre + 1) mx c) ” &&
  “ (1 <= c) ” &&
  “ (2 <= mx) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values))))) ”
  &&  emp
)

noncomputable def solver_entail_wit_5_split_goal_1 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (counts_2 : (List Int)) (c : Int) (mx : Int) (i : Int) (cnt : Int) (PreH1 : (i > n_pre)) (PreH2 : (cnt ≠ (0 : Int))) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values (0 : Int))) ∧ ((Znth k_2 values (0 : Int)) <= (Zlength (values)))))) (PreH7 : (Pre values)) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1))) (PreH10 : ((0 : Int) <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : ((0 : Int) <= c)) (PreH13 : (c <= (i - 1))) (PreH14 : (CountPrefix values n_pre counts_2)) (PreH15 : (MaximumFrequencyPrefix counts_2 i mx c)) (PreH16 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= n_pre)) -> (((0 : Int) <= (Znth k_3 counts_2 (0 : Int))) ∧ ((Znth k_3 counts_2 (0 : Int)) <= n_pre)))) ,
  (Spec values ((Z.quot (n_pre - c) (mx - 1)) - 1))

noncomputable def solver_entail_wit_5_split_goal_2 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (counts_2 : (List Int)) (c : Int) (mx : Int) (i : Int) (cnt : Int) (PreH1 : (i > n_pre)) (PreH2 : (cnt ≠ (0 : Int))) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values (0 : Int))) ∧ ((Znth k_2 values (0 : Int)) <= (Zlength (values)))))) (PreH7 : (Pre values)) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1))) (PreH10 : ((0 : Int) <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : ((0 : Int) <= c)) (PreH13 : (c <= (i - 1))) (PreH14 : (CountPrefix values n_pre counts_2)) (PreH15 : (MaximumFrequencyPrefix counts_2 i mx c)) (PreH16 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= n_pre)) -> (((0 : Int) <= (Znth k_3 counts_2 (0 : Int))) ∧ ((Znth k_3 counts_2 (0 : Int)) <= n_pre)))) ,
  (MaximumFrequencyPrefix counts_2 (n_pre + 1) mx c)

noncomputable def solver_entail_wit_5_split_goal_3 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (counts_2 : (List Int)) (c : Int) (mx : Int) (i : Int) (cnt : Int) (PreH1 : (i > n_pre)) (PreH2 : (cnt ≠ (0 : Int))) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values (0 : Int))) ∧ ((Znth k_2 values (0 : Int)) <= (Zlength (values)))))) (PreH7 : (Pre values)) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1))) (PreH10 : ((0 : Int) <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : ((0 : Int) <= c)) (PreH13 : (c <= (i - 1))) (PreH14 : (CountPrefix values n_pre counts_2)) (PreH15 : (MaximumFrequencyPrefix counts_2 i mx c)) (PreH16 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= n_pre)) -> (((0 : Int) <= (Znth k_3 counts_2 (0 : Int))) ∧ ((Znth k_3 counts_2 (0 : Int)) <= n_pre)))) ,
  (1 <= c)

noncomputable def solver_entail_wit_5_split_goal_4 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (counts_2 : (List Int)) (c : Int) (mx : Int) (i : Int) (cnt : Int) (PreH1 : (i > n_pre)) (PreH2 : (cnt ≠ (0 : Int))) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values (0 : Int))) ∧ ((Znth k_2 values (0 : Int)) <= (Zlength (values)))))) (PreH7 : (Pre values)) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1))) (PreH10 : ((0 : Int) <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : ((0 : Int) <= c)) (PreH13 : (c <= (i - 1))) (PreH14 : (CountPrefix values n_pre counts_2)) (PreH15 : (MaximumFrequencyPrefix counts_2 i mx c)) (PreH16 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= n_pre)) -> (((0 : Int) <= (Znth k_3 counts_2 (0 : Int))) ∧ ((Znth k_3 counts_2 (0 : Int)) <= n_pre)))) ,
  (2 <= mx)

noncomputable def solver_entail_wit_5_split_goal_5 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (counts_2 : (List Int)) (c : Int) (mx : Int) (i : Int) (cnt : Int) (PreH1 : (i > n_pre)) (PreH2 : (cnt ≠ (0 : Int))) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values (0 : Int))) ∧ ((Znth k_2 values (0 : Int)) <= (Zlength (values)))))) (PreH7 : (Pre values)) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1))) (PreH10 : ((0 : Int) <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : ((0 : Int) <= c)) (PreH13 : (c <= (i - 1))) (PreH14 : (CountPrefix values n_pre counts_2)) (PreH15 : (MaximumFrequencyPrefix counts_2 i mx c)) (PreH16 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 <= n_pre)) -> (((0 : Int) <= (Znth k_3 counts_2 (0 : Int))) ∧ ((Znth k_3 counts_2 (0 : Int)) <= n_pre)))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))

noncomputable def solver_return_wit_1 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (counts : (List Int)) (cnt : Int) (mx : Int) (c : Int) (ans : Int) (PreH1 : (cnt ≠ (0 : Int))) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH6 : (Pre values)) (PreH7 : (2 <= mx)) (PreH8 : (mx <= n_pre)) (PreH9 : (1 <= c)) (PreH10 : (c <= n_pre)) (PreH11 : (ans = ((Z.quot (n_pre - c) (mx - 1)) - 1))) (PreH12 : (CountPrefix values n_pre counts)) (PreH13 : (MaximumFrequencyPrefix counts (n_pre + 1) mx c)) (PreH14 : (Spec values ans)) ,
  (intArray.full a_pre n_pre values)
|--
  “ (Spec values ans) ”
  &&  (intArray.full a_pre n_pre values)

noncomputable def solver_partial_solve_wit_1_pure : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (PreH1 : (2 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 100000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> ((1 <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= (Zlength (values)))))) (PreH4 : (Pre values)) (PreH5 : (n_pre = (Zlength (values)))) ,
  ((( &( "cnt" ) )) # Ptr |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre values)
|--
  “ ((0 : Int) <= (n_pre + 1)) ” &&
  “ ((n_pre + 1) = (n_pre + 1)) ” &&
  “ (sizeof(INT) = sizeof(INT)) ”

noncomputable def solver_partial_solve_wit_1_aux : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (PreH1 : (2 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 100000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> ((1 <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= (Zlength (values)))))) (PreH4 : (Pre values)) (PreH5 : (n_pre = (Zlength (values)))) ,
  (intArray.full a_pre n_pre values)
|--
  “ ((0 : Int) <= (n_pre + 1)) ” &&
  “ ((n_pre + 1) = (n_pre + 1)) ” &&
  “ (sizeof(INT) = sizeof(INT)) ” &&
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 100000) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (values)))) -> ((1 <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= (Zlength (values))))) ” &&
  “ (Pre values) ” &&
  “ (n_pre = (Zlength (values))) ”
  &&  (intArray.full a_pre n_pre values)

noncomputable def solver_partial_solve_wit_1 : Prop := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux

noncomputable def solver_partial_solve_wit_2 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (counts : (List Int)) (i : Int) (c : Int) (mx : Int) (cnt : Int) (PreH1 : (i < n_pre)) (PreH2 : (cnt ≠ (0 : Int))) (PreH3 : (mx = (0 : Int))) (PreH4 : (c = (0 : Int))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH9 : (Pre values)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (CountPrefix values i counts)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= i)))) ,
  (intArray.full a_pre n_pre values)
  ** (intArray.full cnt (n_pre + 1) counts)
|--
  “ (i < n_pre) ” &&
  “ (cnt ≠ (0 : Int)) ” &&
  “ (mx = (0 : Int)) ” &&
  “ (c = (0 : Int)) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values))))) ” &&
  “ (Pre values) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (CountPrefix values i counts) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= i))) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i values (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre values)
  ** (intArray.full cnt (n_pre + 1) counts)

noncomputable def solver_partial_solve_wit_3 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (counts : (List Int)) (i : Int) (c : Int) (mx : Int) (cnt : Int) (PreH1 : (i < n_pre)) (PreH2 : (cnt ≠ (0 : Int))) (PreH3 : (mx = (0 : Int))) (PreH4 : (c = (0 : Int))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH9 : (Pre values)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (CountPrefix values i counts)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= i)))) ,
  (intArray.full a_pre n_pre values)
  ** (intArray.full cnt (n_pre + 1) counts)
|--
  “ (i < n_pre) ” &&
  “ (cnt ≠ (0 : Int)) ” &&
  “ (mx = (0 : Int)) ” &&
  “ (c = (0 : Int)) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values))))) ” &&
  “ (Pre values) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (CountPrefix values i counts) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= i))) ”
  &&  (((cnt + ((Znth i values (0 : Int)) * sizeof(INT)))) # Int |-> ((Znth (Znth i values (0 : Int)) counts (0 : Int))))
  ** (intArray.missing_i cnt (Znth i values (0 : Int)) (0 : Int) (n_pre + 1) counts)
  ** (intArray.full a_pre n_pre values)

noncomputable def solver_partial_solve_wit_4 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (counts : (List Int)) (i : Int) (c : Int) (mx : Int) (cnt : Int) (PreH1 : (i < n_pre)) (PreH2 : (cnt ≠ (0 : Int))) (PreH3 : (mx = (0 : Int))) (PreH4 : (c = (0 : Int))) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH9 : (Pre values)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (CountPrefix values i counts)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= i)))) ,
  (intArray.full cnt (n_pre + 1) counts)
  ** (intArray.full a_pre n_pre values)
|--
  “ (i < n_pre) ” &&
  “ (cnt ≠ (0 : Int)) ” &&
  “ (mx = (0 : Int)) ” &&
  “ (c = (0 : Int)) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values))))) ” &&
  “ (Pre values) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (CountPrefix values i counts) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= i))) ”
  &&  (((cnt + ((Znth i values (0 : Int)) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i cnt (Znth i values (0 : Int)) (0 : Int) (n_pre + 1) counts)
  ** (intArray.full a_pre n_pre values)

noncomputable def solver_partial_solve_wit_5 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (counts : (List Int)) (c : Int) (mx : Int) (i : Int) (cnt : Int) (PreH1 : (i <= n_pre)) (PreH2 : (cnt ≠ (0 : Int))) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH7 : (Pre values)) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1))) (PreH10 : ((0 : Int) <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : ((0 : Int) <= c)) (PreH13 : (c <= (i - 1))) (PreH14 : (CountPrefix values n_pre counts)) (PreH15 : (MaximumFrequencyPrefix counts i mx c)) (PreH16 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= n_pre)))) ,
  (intArray.full a_pre n_pre values)
  ** (intArray.full cnt (n_pre + 1) counts)
|--
  “ (i <= n_pre) ” &&
  “ (cnt ≠ (0 : Int)) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values))))) ” &&
  “ (Pre values) ” &&
  “ (1 <= i) ” &&
  “ (i <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= mx) ” &&
  “ (mx <= n_pre) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= (i - 1)) ” &&
  “ (CountPrefix values n_pre counts) ” &&
  “ (MaximumFrequencyPrefix counts i mx c) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= n_pre))) ”
  &&  (((cnt + (i * sizeof(INT)))) # Int |-> ((Znth i counts (0 : Int))))
  ** (intArray.missing_i cnt i (0 : Int) (n_pre + 1) counts)
  ** (intArray.full a_pre n_pre values)

noncomputable def solver_partial_solve_wit_6 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (counts : (List Int)) (c : Int) (mx : Int) (i : Int) (cnt : Int) (PreH1 : ((Znth i counts (0 : Int)) > mx)) (PreH2 : (i <= n_pre)) (PreH3 : (cnt ≠ (0 : Int))) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH8 : (Pre values)) (PreH9 : (1 <= i)) (PreH10 : (i <= (n_pre + 1))) (PreH11 : ((0 : Int) <= mx)) (PreH12 : (mx <= n_pre)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= (i - 1))) (PreH15 : (CountPrefix values n_pre counts)) (PreH16 : (MaximumFrequencyPrefix counts i mx c)) (PreH17 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= n_pre)))) ,
  (intArray.full cnt (n_pre + 1) counts)
  ** (intArray.full a_pre n_pre values)
|--
  “ ((Znth i counts (0 : Int)) > mx) ” &&
  “ (i <= n_pre) ” &&
  “ (cnt ≠ (0 : Int)) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values))))) ” &&
  “ (Pre values) ” &&
  “ (1 <= i) ” &&
  “ (i <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= mx) ” &&
  “ (mx <= n_pre) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= (i - 1)) ” &&
  “ (CountPrefix values n_pre counts) ” &&
  “ (MaximumFrequencyPrefix counts i mx c) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= n_pre))) ”
  &&  (((cnt + (i * sizeof(INT)))) # Int |-> ((Znth i counts (0 : Int))))
  ** (intArray.missing_i cnt i (0 : Int) (n_pre + 1) counts)
  ** (intArray.full a_pre n_pre values)

noncomputable def solver_partial_solve_wit_7 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (counts : (List Int)) (c : Int) (mx : Int) (i : Int) (cnt : Int) (PreH1 : ((Znth i counts (0 : Int)) <= mx)) (PreH2 : (i <= n_pre)) (PreH3 : (cnt ≠ (0 : Int))) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH8 : (Pre values)) (PreH9 : (1 <= i)) (PreH10 : (i <= (n_pre + 1))) (PreH11 : ((0 : Int) <= mx)) (PreH12 : (mx <= n_pre)) (PreH13 : ((0 : Int) <= c)) (PreH14 : (c <= (i - 1))) (PreH15 : (CountPrefix values n_pre counts)) (PreH16 : (MaximumFrequencyPrefix counts i mx c)) (PreH17 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= n_pre)))) ,
  (intArray.full cnt (n_pre + 1) counts)
  ** (intArray.full a_pre n_pre values)
|--
  “ ((Znth i counts (0 : Int)) <= mx) ” &&
  “ (i <= n_pre) ” &&
  “ (cnt ≠ (0 : Int)) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values))))) ” &&
  “ (Pre values) ” &&
  “ (1 <= i) ” &&
  “ (i <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= mx) ” &&
  “ (mx <= n_pre) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c <= (i - 1)) ” &&
  “ (CountPrefix values n_pre counts) ” &&
  “ (MaximumFrequencyPrefix counts i mx c) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 <= n_pre)) -> (((0 : Int) <= (Znth k_2 counts (0 : Int))) ∧ ((Znth k_2 counts (0 : Int)) <= n_pre))) ”
  &&  (((cnt + (i * sizeof(INT)))) # Int |-> ((Znth i counts (0 : Int))))
  ** (intArray.missing_i cnt i (0 : Int) (n_pre + 1) counts)
  ** (intArray.full a_pre n_pre values)

noncomputable def solver_partial_solve_wit_8 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (counts : (List Int)) (cnt : Int) (mx : Int) (c : Int) (ans : Int) (PreH1 : (cnt ≠ (0 : Int))) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values)))))) (PreH6 : (Pre values)) (PreH7 : (2 <= mx)) (PreH8 : (mx <= n_pre)) (PreH9 : (1 <= c)) (PreH10 : (c <= n_pre)) (PreH11 : (ans = ((Z.quot (n_pre - c) (mx - 1)) - 1))) (PreH12 : (CountPrefix values n_pre counts)) (PreH13 : (MaximumFrequencyPrefix counts (n_pre + 1) mx c)) (PreH14 : (Spec values ans)) ,
  (intArray.full a_pre n_pre values)
  ** (intArray.full cnt (n_pre + 1) counts)
|--
  “ (cnt ≠ (0 : Int)) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ (2 <= (Zlength (values))) ” &&
  “ ((Zlength (values)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (values)))) -> ((1 <= (Znth k values (0 : Int))) ∧ ((Znth k values (0 : Int)) <= (Zlength (values))))) ” &&
  “ (Pre values) ” &&
  “ (2 <= mx) ” &&
  “ (mx <= n_pre) ” &&
  “ (1 <= c) ” &&
  “ (c <= n_pre) ” &&
  “ (ans = ((Z.quot (n_pre - c) (mx - 1)) - 1)) ” &&
  “ (CountPrefix values n_pre counts) ” &&
  “ (MaximumFrequencyPrefix counts (n_pre + 1) mx c) ” &&
  “ (Spec values ans) ”
  &&  (intArray.full cnt ((Zlength (values)) + 1) counts)
  ** (intArray.full a_pre n_pre values)


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
  proof_of_solver_safety_wit_15 : solver_safety_wit_15
  proof_of_solver_safety_wit_16 : solver_safety_wit_16
  proof_of_solver_safety_wit_17 : solver_safety_wit_17
  proof_of_solver_safety_wit_18 : solver_safety_wit_18
  proof_of_solver_return_wit_1 : solver_return_wit_1
  proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2
  proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3
  proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4
  proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5
  proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6
  proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7
  proof_of_solver_partial_solve_wit_8 : solver_partial_solve_wit_8
  proof_of_solver_safety_wit_13 : solver_safety_wit_13
  proof_of_solver_safety_wit_14 : solver_safety_wit_14
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_2 : solver_entail_wit_2
  proof_of_solver_entail_wit_3 : solver_entail_wit_3
  proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1
  proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2
  proof_of_solver_entail_wit_4_3 : solver_entail_wit_4_3
  proof_of_solver_entail_wit_5 : solver_entail_wit_5

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_goal
