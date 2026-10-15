import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P009_1696B_nit_destroys_the_universe_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100000)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (input)))) -> (((0 : Int) <= (Znth i input (0 : Int))) ∧ ((Znth i input (0 : Int)) <= 1000000000)))) ,
  ((( &( "inside" ) )) # Int |->_)
  ** ((( &( "runs" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 200005)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100000)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (input)))) -> (((0 : Int) <= (Znth i input (0 : Int))) ∧ ((Znth i input (0 : Int)) <= 1000000000)))) ,
  ((( &( "runs" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 200005)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100000)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (input)))) -> (((0 : Int) <= (Znth i input (0 : Int))) ∧ ((Znth i input (0 : Int)) <= 1000000000)))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "inside" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "runs" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 200005)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (inside : Int) (runs : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (1 <= (Zlength (input)))) (PreH4 : ((Zlength (input)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= runs)) (PreH9 : (runs <= i)) (PreH10 : ((0 : Int) <= inside)) (PreH11 : (inside <= 1)) (PreH12 : (ScanState input i runs inside)) ,
  (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "runs" ) )) # Int |-> (runs))
  ** ((( &( "inside" ) )) # Int |-> (inside))
  ** (intArray.undef_seg a_pre n_pre 200005)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (inside : Int) (runs : Int) (i : Int) (PreH1 : (inside = (0 : Int))) (PreH2 : ((Znth i input (0 : Int)) ≠ (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= runs)) (PreH11 : (runs <= i)) (PreH12 : ((0 : Int) <= inside)) (PreH13 : (inside <= 1)) (PreH14 : (ScanState input i runs inside)) ,
  (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "runs" ) )) # Int |-> (runs))
  ** ((( &( "inside" ) )) # Int |-> (inside))
  ** (intArray.undef_seg a_pre n_pre 200005)
|--
  “ ((runs + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (runs + 1)) ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (inside : Int) (runs : Int) (i : Int) (PreH1 : (inside = (0 : Int))) (PreH2 : ((Znth i input (0 : Int)) ≠ (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= runs)) (PreH11 : (runs <= i)) (PreH12 : ((0 : Int) <= inside)) (PreH13 : (inside <= 1)) (PreH14 : (ScanState input i runs inside)) ,
  (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "runs" ) )) # Int |-> ((runs + 1)))
  ** ((( &( "inside" ) )) # Int |-> (inside))
  ** (intArray.undef_seg a_pre n_pre 200005)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_7 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (inside : Int) (runs : Int) (i : Int) (PreH1 : (inside = (0 : Int))) (PreH2 : ((Znth i input (0 : Int)) ≠ (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= runs)) (PreH11 : (runs <= i)) (PreH12 : ((0 : Int) <= inside)) (PreH13 : (inside <= 1)) (PreH14 : (ScanState input i runs inside)) ,
  (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "runs" ) )) # Int |-> ((runs + 1)))
  ** ((( &( "inside" ) )) # Int |-> (1))
  ** (intArray.undef_seg a_pre n_pre 200005)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_8 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (inside : Int) (runs : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) = (0 : Int))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= (Zlength (input)))) (PreH5 : ((Zlength (input)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= runs)) (PreH10 : (runs <= i)) (PreH11 : ((0 : Int) <= inside)) (PreH12 : (inside <= 1)) (PreH13 : (ScanState input i runs inside)) ,
  (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "runs" ) )) # Int |-> (runs))
  ** ((( &( "inside" ) )) # Int |-> (inside))
  ** (intArray.undef_seg a_pre n_pre 200005)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_9 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (inside : Int) (runs : Int) (i : Int) (PreH1 : (inside ≠ (0 : Int))) (PreH2 : ((Znth i input (0 : Int)) ≠ (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= runs)) (PreH11 : (runs <= i)) (PreH12 : ((0 : Int) <= inside)) (PreH13 : (inside <= 1)) (PreH14 : (ScanState input i runs inside)) ,
  (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "runs" ) )) # Int |-> (runs))
  ** ((( &( "inside" ) )) # Int |-> (inside))
  ** (intArray.undef_seg a_pre n_pre 200005)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_10 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (inside : Int) (runs : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) = (0 : Int))) (PreH2 : (inside = (0 : Int))) (PreH3 : ((Znth i input (0 : Int)) ≠ (0 : Int))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (1 <= (Zlength (input)))) (PreH7 : ((Zlength (input)) <= 100000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((0 : Int) <= runs)) (PreH12 : (runs <= i)) (PreH13 : ((0 : Int) <= inside)) (PreH14 : (inside <= 1)) (PreH15 : (ScanState input i runs inside)) ,
  (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "runs" ) )) # Int |-> ((runs + 1)))
  ** ((( &( "inside" ) )) # Int |-> (1))
  ** (intArray.undef_seg a_pre n_pre 200005)
|--
  “ False ”

noncomputable def solver_safety_wit_11 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (inside : Int) (runs : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) ≠ (0 : Int))) (PreH2 : ((Znth i input (0 : Int)) = (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= runs)) (PreH11 : (runs <= i)) (PreH12 : ((0 : Int) <= inside)) (PreH13 : (inside <= 1)) (PreH14 : (ScanState input i runs inside)) ,
  (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "runs" ) )) # Int |-> (runs))
  ** ((( &( "inside" ) )) # Int |-> (inside))
  ** (intArray.undef_seg a_pre n_pre 200005)
|--
  “ False ”

noncomputable def solver_safety_wit_12 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (inside : Int) (runs : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) = (0 : Int))) (PreH2 : (inside ≠ (0 : Int))) (PreH3 : ((Znth i input (0 : Int)) ≠ (0 : Int))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (1 <= (Zlength (input)))) (PreH7 : ((Zlength (input)) <= 100000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((0 : Int) <= runs)) (PreH12 : (runs <= i)) (PreH13 : ((0 : Int) <= inside)) (PreH14 : (inside <= 1)) (PreH15 : (ScanState input i runs inside)) ,
  (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "runs" ) )) # Int |-> (runs))
  ** ((( &( "inside" ) )) # Int |-> (inside))
  ** (intArray.undef_seg a_pre n_pre 200005)
|--
  “ False ”

noncomputable def solver_safety_wit_13 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (inside : Int) (runs : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) = (0 : Int))) (PreH2 : ((Znth i input (0 : Int)) = (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= runs)) (PreH11 : (runs <= i)) (PreH12 : ((0 : Int) <= inside)) (PreH13 : (inside <= 1)) (PreH14 : (ScanState input i runs inside)) ,
  (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "runs" ) )) # Int |-> (runs))
  ** ((( &( "inside" ) )) # Int |-> (inside))
  ** (intArray.undef_seg a_pre n_pre 200005)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_14 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (inside : Int) (runs : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) = (0 : Int))) (PreH2 : ((Znth i input (0 : Int)) = (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= runs)) (PreH11 : (runs <= i)) (PreH12 : ((0 : Int) <= inside)) (PreH13 : (inside <= 1)) (PreH14 : (ScanState input i runs inside)) ,
  (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "runs" ) )) # Int |-> (runs))
  ** ((( &( "inside" ) )) # Int |-> ((0 : Int)))
  ** (intArray.undef_seg a_pre n_pre 200005)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_15 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (inside : Int) (runs : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) ≠ (0 : Int))) (PreH2 : (inside = (0 : Int))) (PreH3 : ((Znth i input (0 : Int)) ≠ (0 : Int))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (1 <= (Zlength (input)))) (PreH7 : ((Zlength (input)) <= 100000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((0 : Int) <= runs)) (PreH12 : (runs <= i)) (PreH13 : ((0 : Int) <= inside)) (PreH14 : (inside <= 1)) (PreH15 : (ScanState input i runs inside)) ,
  (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "runs" ) )) # Int |-> ((runs + 1)))
  ** ((( &( "inside" ) )) # Int |-> (1))
  ** (intArray.undef_seg a_pre n_pre 200005)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_16 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (inside : Int) (runs : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) ≠ (0 : Int))) (PreH2 : (inside ≠ (0 : Int))) (PreH3 : ((Znth i input (0 : Int)) ≠ (0 : Int))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (1 <= (Zlength (input)))) (PreH7 : ((Zlength (input)) <= 100000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((0 : Int) <= runs)) (PreH12 : (runs <= i)) (PreH13 : ((0 : Int) <= inside)) (PreH14 : (inside <= 1)) (PreH15 : (ScanState input i runs inside)) ,
  (intArray.full a_pre n_pre input)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "runs" ) )) # Int |-> (runs))
  ** ((( &( "inside" ) )) # Int |-> (inside))
  ** (intArray.undef_seg a_pre n_pre 200005)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_17 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (inside : Int) (runs : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (1 <= (Zlength (input)))) (PreH4 : ((Zlength (input)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= runs)) (PreH9 : (runs <= i)) (PreH10 : ((0 : Int) <= inside)) (PreH11 : (inside <= 1)) (PreH12 : (ScanState input i runs inside)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "runs" ) )) # Int |-> (runs))
  ** ((( &( "inside" ) )) # Int |-> (inside))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 200005)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_18 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (inside : Int) (runs : Int) (i : Int) (PreH1 : (runs > 2)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= (Zlength (input)))) (PreH5 : ((Zlength (input)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= runs)) (PreH10 : (runs <= i)) (PreH11 : ((0 : Int) <= inside)) (PreH12 : (inside <= 1)) (PreH13 : (ScanState input i runs inside)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "runs" ) )) # Int |-> (runs))
  ** ((( &( "inside" ) )) # Int |-> (inside))
  ** (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 200005)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100000)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (input)))) -> (((0 : Int) <= (Znth i input (0 : Int))) ∧ ((Znth i input (0 : Int)) <= 1000000000)))) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 200005)
|--
  “ (n_pre = (Zlength (input))) ” &&
  “ (1 <= (Zlength (input))) ” &&
  “ ((Zlength (input)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 1) ” &&
  “ (ScanState input (0 : Int) (0 : Int) (0 : Int)) ”
  &&  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 200005)
) \/
(
forall (n_pre : Int) (input : (List Int)) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100000)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (input)))) -> (((0 : Int) <= (Znth i input (0 : Int))) ∧ ((Znth i input (0 : Int)) <= 1000000000)))) ,
  TT && emp 
|--
  “ (ScanState input (0 : Int) (0 : Int) (0 : Int)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000))) ”
  &&  emp
)

noncomputable def solver_entail_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100000)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (input)))) -> (((0 : Int) <= (Znth i input (0 : Int))) ∧ ((Znth i input (0 : Int)) <= 1000000000)))) ,
  (ScanState input (0 : Int) (0 : Int) (0 : Int))

noncomputable def solver_entail_wit_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100000)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (input)))) -> (((0 : Int) <= (Znth i input (0 : Int))) ∧ ((Znth i input (0 : Int)) <= 1000000000)))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000)))

noncomputable def solver_entail_wit_2_1 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (inside : Int) (runs : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) = (0 : Int))) (PreH2 : ((Znth i input (0 : Int)) = (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= runs)) (PreH11 : (runs <= i)) (PreH12 : ((0 : Int) <= inside)) (PreH13 : (inside <= 1)) (PreH14 : (ScanState input i runs inside)) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 200005)
|--
  “ (n_pre = (Zlength (input))) ” &&
  “ (1 <= (Zlength (input))) ” &&
  “ ((Zlength (input)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= runs) ” &&
  “ (runs <= (i + 1)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 1) ” &&
  “ (ScanState input (i + 1) runs (0 : Int)) ”
  &&  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 200005)
) \/
(
forall (n_pre : Int) (input : (List Int)) (inside : Int) (runs : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) = (0 : Int))) (PreH2 : ((Znth i input (0 : Int)) = (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= runs)) (PreH11 : (runs <= i)) (PreH12 : ((0 : Int) <= inside)) (PreH13 : (inside <= 1)) (PreH14 : (ScanState input i runs inside)) ,
  TT && emp 
|--
  “ (ScanState input (i + 1) runs (0 : Int)) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (inside : Int) (runs : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) = (0 : Int))) (PreH2 : ((Znth i input (0 : Int)) = (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= runs)) (PreH11 : (runs <= i)) (PreH12 : ((0 : Int) <= inside)) (PreH13 : (inside <= 1)) (PreH14 : (ScanState input i runs inside)) ,
  (ScanState input (i + 1) runs (0 : Int))

noncomputable def solver_entail_wit_2_2 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (inside : Int) (runs : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) ≠ (0 : Int))) (PreH2 : (inside = (0 : Int))) (PreH3 : ((Znth i input (0 : Int)) ≠ (0 : Int))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (1 <= (Zlength (input)))) (PreH7 : ((Zlength (input)) <= 100000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((0 : Int) <= runs)) (PreH12 : (runs <= i)) (PreH13 : ((0 : Int) <= inside)) (PreH14 : (inside <= 1)) (PreH15 : (ScanState input i runs inside)) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 200005)
|--
  “ (n_pre = (Zlength (input))) ” &&
  “ (1 <= (Zlength (input))) ” &&
  “ ((Zlength (input)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= (runs + 1)) ” &&
  “ ((runs + 1) <= (i + 1)) ” &&
  “ ((0 : Int) <= 1) ” &&
  “ (1 <= 1) ” &&
  “ (ScanState input (i + 1) (runs + 1) 1) ”
  &&  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 200005)
) \/
(
forall (n_pre : Int) (input : (List Int)) (inside : Int) (runs : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) ≠ (0 : Int))) (PreH2 : (inside = (0 : Int))) (PreH3 : ((Znth i input (0 : Int)) ≠ (0 : Int))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (1 <= (Zlength (input)))) (PreH7 : ((Zlength (input)) <= 100000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((0 : Int) <= runs)) (PreH12 : (runs <= i)) (PreH13 : ((0 : Int) <= inside)) (PreH14 : (inside <= 1)) (PreH15 : (ScanState input i runs inside)) ,
  TT && emp 
|--
  “ (ScanState input (i + 1) (runs + 1) 1) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (inside : Int) (runs : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) ≠ (0 : Int))) (PreH2 : (inside = (0 : Int))) (PreH3 : ((Znth i input (0 : Int)) ≠ (0 : Int))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (1 <= (Zlength (input)))) (PreH7 : ((Zlength (input)) <= 100000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((0 : Int) <= runs)) (PreH12 : (runs <= i)) (PreH13 : ((0 : Int) <= inside)) (PreH14 : (inside <= 1)) (PreH15 : (ScanState input i runs inside)) ,
  (ScanState input (i + 1) (runs + 1) 1)

noncomputable def solver_entail_wit_2_3 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (inside : Int) (runs : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) ≠ (0 : Int))) (PreH2 : (inside ≠ (0 : Int))) (PreH3 : ((Znth i input (0 : Int)) ≠ (0 : Int))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (1 <= (Zlength (input)))) (PreH7 : ((Zlength (input)) <= 100000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((0 : Int) <= runs)) (PreH12 : (runs <= i)) (PreH13 : ((0 : Int) <= inside)) (PreH14 : (inside <= 1)) (PreH15 : (ScanState input i runs inside)) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 200005)
|--
  “ (n_pre = (Zlength (input))) ” &&
  “ (1 <= (Zlength (input))) ” &&
  “ ((Zlength (input)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= runs) ” &&
  “ (runs <= (i + 1)) ” &&
  “ ((0 : Int) <= inside) ” &&
  “ (inside <= 1) ” &&
  “ (ScanState input (i + 1) runs inside) ”
  &&  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 200005)
) \/
(
forall (n_pre : Int) (input : (List Int)) (inside : Int) (runs : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) ≠ (0 : Int))) (PreH2 : (inside ≠ (0 : Int))) (PreH3 : ((Znth i input (0 : Int)) ≠ (0 : Int))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (1 <= (Zlength (input)))) (PreH7 : ((Zlength (input)) <= 100000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((0 : Int) <= runs)) (PreH12 : (runs <= i)) (PreH13 : ((0 : Int) <= inside)) (PreH14 : (inside <= 1)) (PreH15 : (ScanState input i runs inside)) ,
  TT && emp 
|--
  “ (ScanState input (i + 1) runs inside) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_3_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (inside : Int) (runs : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) ≠ (0 : Int))) (PreH2 : (inside ≠ (0 : Int))) (PreH3 : ((Znth i input (0 : Int)) ≠ (0 : Int))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (1 <= (Zlength (input)))) (PreH7 : ((Zlength (input)) <= 100000)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((0 : Int) <= runs)) (PreH12 : (runs <= i)) (PreH13 : ((0 : Int) <= inside)) (PreH14 : (inside <= 1)) (PreH15 : (ScanState input i runs inside)) ,
  (ScanState input (i + 1) runs inside)

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (inside : Int) (runs : Int) (i : Int) (PreH1 : (runs > 2)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= (Zlength (input)))) (PreH5 : ((Zlength (input)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= runs)) (PreH10 : (runs <= i)) (PreH11 : ((0 : Int) <= inside)) (PreH12 : (inside <= 1)) (PreH13 : (ScanState input i runs inside)) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 200005)
|--
  “ (Spec input 2) ”
  &&  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 200005)
) \/
(
forall (n_pre : Int) (input : (List Int)) (inside : Int) (runs : Int) (i : Int) (PreH1 : (runs > 2)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= (Zlength (input)))) (PreH5 : ((Zlength (input)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= runs)) (PreH10 : (runs <= i)) (PreH11 : ((0 : Int) <= inside)) (PreH12 : (inside <= 1)) (PreH13 : (ScanState input i runs inside)) ,
  TT && emp 
|--
  “ (Spec input 2) ”
  &&  emp
)

noncomputable def solver_return_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (inside : Int) (runs : Int) (i : Int) (PreH1 : (runs > 2)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= (Zlength (input)))) (PreH5 : ((Zlength (input)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= runs)) (PreH10 : (runs <= i)) (PreH11 : ((0 : Int) <= inside)) (PreH12 : (inside <= 1)) (PreH13 : (ScanState input i runs inside)) ,
  (Spec input 2)

noncomputable def solver_return_wit_2 : Prop :=
  (
forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (inside : Int) (runs : Int) (i : Int) (PreH1 : (runs <= 2)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= (Zlength (input)))) (PreH5 : ((Zlength (input)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= runs)) (PreH10 : (runs <= i)) (PreH11 : ((0 : Int) <= inside)) (PreH12 : (inside <= 1)) (PreH13 : (ScanState input i runs inside)) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 200005)
|--
  “ (Spec input runs) ”
  &&  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 200005)
) \/
(
forall (n_pre : Int) (input : (List Int)) (inside : Int) (runs : Int) (i : Int) (PreH1 : (runs <= 2)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= (Zlength (input)))) (PreH5 : ((Zlength (input)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= runs)) (PreH10 : (runs <= i)) (PreH11 : ((0 : Int) <= inside)) (PreH12 : (inside <= 1)) (PreH13 : (ScanState input i runs inside)) ,
  TT && emp 
|--
  “ (Spec input runs) ”
  &&  emp
)

noncomputable def solver_return_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (input : (List Int)) (inside : Int) (runs : Int) (i : Int) (PreH1 : (runs <= 2)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= (Zlength (input)))) (PreH5 : ((Zlength (input)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= runs)) (PreH10 : (runs <= i)) (PreH11 : ((0 : Int) <= inside)) (PreH12 : (inside <= 1)) (PreH13 : (ScanState input i runs inside)) ,
  (Spec input runs)

noncomputable def solver_partial_solve_wit_1 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (inside : Int) (runs : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (1 <= (Zlength (input)))) (PreH4 : ((Zlength (input)) <= 100000)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000)))) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= runs)) (PreH9 : (runs <= i)) (PreH10 : ((0 : Int) <= inside)) (PreH11 : (inside <= 1)) (PreH12 : (ScanState input i runs inside)) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 200005)
|--
  “ (i < n_pre) ” &&
  “ (n_pre = (Zlength (input))) ” &&
  “ (1 <= (Zlength (input))) ” &&
  “ ((Zlength (input)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= runs) ” &&
  “ (runs <= i) ” &&
  “ ((0 : Int) <= inside) ” &&
  “ (inside <= 1) ” &&
  “ (ScanState input i runs inside) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i input (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre input)
  ** (intArray.undef_seg a_pre n_pre 200005)

noncomputable def solver_partial_solve_wit_2 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (inside : Int) (runs : Int) (i : Int) (PreH1 : (inside = (0 : Int))) (PreH2 : ((Znth i input (0 : Int)) ≠ (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= runs)) (PreH11 : (runs <= i)) (PreH12 : ((0 : Int) <= inside)) (PreH13 : (inside <= 1)) (PreH14 : (ScanState input i runs inside)) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 200005)
|--
  “ (inside = (0 : Int)) ” &&
  “ ((Znth i input (0 : Int)) ≠ (0 : Int)) ” &&
  “ (i < n_pre) ” &&
  “ (n_pre = (Zlength (input))) ” &&
  “ (1 <= (Zlength (input))) ” &&
  “ ((Zlength (input)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= runs) ” &&
  “ (runs <= i) ” &&
  “ ((0 : Int) <= inside) ” &&
  “ (inside <= 1) ” &&
  “ (ScanState input i runs inside) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i input (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre input)
  ** (intArray.undef_seg a_pre n_pre 200005)

noncomputable def solver_partial_solve_wit_3 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (inside : Int) (runs : Int) (i : Int) (PreH1 : ((Znth i input (0 : Int)) = (0 : Int))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= (Zlength (input)))) (PreH5 : ((Zlength (input)) <= 100000)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= runs)) (PreH10 : (runs <= i)) (PreH11 : ((0 : Int) <= inside)) (PreH12 : (inside <= 1)) (PreH13 : (ScanState input i runs inside)) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 200005)
|--
  “ ((Znth i input (0 : Int)) = (0 : Int)) ” &&
  “ (i < n_pre) ” &&
  “ (n_pre = (Zlength (input))) ” &&
  “ (1 <= (Zlength (input))) ” &&
  “ ((Zlength (input)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= runs) ” &&
  “ (runs <= i) ” &&
  “ ((0 : Int) <= inside) ” &&
  “ (inside <= 1) ” &&
  “ (ScanState input i runs inside) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i input (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre input)
  ** (intArray.undef_seg a_pre n_pre 200005)

noncomputable def solver_partial_solve_wit_4 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (input : (List Int)) (inside : Int) (runs : Int) (i : Int) (PreH1 : (inside ≠ (0 : Int))) (PreH2 : ((Znth i input (0 : Int)) ≠ (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000)))) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((0 : Int) <= runs)) (PreH11 : (runs <= i)) (PreH12 : ((0 : Int) <= inside)) (PreH13 : (inside <= 1)) (PreH14 : (ScanState input i runs inside)) ,
  (intArray.full a_pre n_pre input)
  ** (intArray.undef_seg a_pre n_pre 200005)
|--
  “ (inside ≠ (0 : Int)) ” &&
  “ ((Znth i input (0 : Int)) ≠ (0 : Int)) ” &&
  “ (i < n_pre) ” &&
  “ (n_pre = (Zlength (input))) ” &&
  “ (1 <= (Zlength (input))) ” &&
  “ ((Zlength (input)) <= 100000) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (Zlength (input)))) -> (((0 : Int) <= (Znth k input (0 : Int))) ∧ ((Znth k input (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= runs) ” &&
  “ (runs <= i) ” &&
  “ ((0 : Int) <= inside) ” &&
  “ (inside <= 1) ” &&
  “ (ScanState input i runs inside) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i input (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre input)
  ** (intArray.undef_seg a_pre n_pre 200005)


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
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2
  proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3
  proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1
  proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2
  proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3
  proof_of_solver_return_wit_1 : solver_return_wit_1
  proof_of_solver_return_wit_2 : solver_return_wit_2

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_goal
