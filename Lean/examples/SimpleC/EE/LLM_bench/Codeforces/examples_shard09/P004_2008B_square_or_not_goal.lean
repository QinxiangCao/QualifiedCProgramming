import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P004_2008B_square_or_not_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P004_2008B_square_or_not_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P004_2008B_square_or_not_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P004_2008B_square_or_not_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((Zlength (bits)) = n_pre)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((Znth i bits (0 : Int)) = 48) ∨ ((Znth i bits (0 : Int)) = 49)))) (PreH5 : (Pre bits)) ,
  ((( &( "r" ) )) # Int |->_)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (charArray.full s_pre n_pre bits)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (r : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((Zlength (bits)) = n_pre)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH5 : (Pre bits)) (PreH6 : ((0 : Int) <= r)) (PreH7 : (r <= 447)) (PreH8 : ((r * r) <= n_pre)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** (charArray.full s_pre n_pre bits)
|--
  “ (((r + 1) * (r + 1)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((r + 1) * (r + 1))) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (r : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((Zlength (bits)) = n_pre)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH5 : (Pre bits)) (PreH6 : ((0 : Int) <= r)) (PreH7 : (r <= 447)) (PreH8 : ((r * r) <= n_pre)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** (charArray.full s_pre n_pre bits)
|--
  “ ((r + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (r + 1)) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (r : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((Zlength (bits)) = n_pre)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH5 : (Pre bits)) (PreH6 : ((0 : Int) <= r)) (PreH7 : (r <= 447)) (PreH8 : ((r * r) <= n_pre)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** (charArray.full s_pre n_pre bits)
|--
  “ ((r + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (r + 1)) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (r : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((Zlength (bits)) = n_pre)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH5 : (Pre bits)) (PreH6 : ((0 : Int) <= r)) (PreH7 : (r <= 447)) (PreH8 : ((r * r) <= n_pre)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** (charArray.full s_pre n_pre bits)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (r : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((Zlength (bits)) = n_pre)) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH5 : (Pre bits)) (PreH6 : ((0 : Int) <= r)) (PreH7 : (r <= 447)) (PreH8 : ((r * r) <= n_pre)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** (charArray.full s_pre n_pre bits)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_7 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (r : Int) (PreH1 : (((r + 1) * (r + 1)) <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH6 : (Pre bits)) (PreH7 : ((0 : Int) <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r) <= n_pre)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** (charArray.full s_pre n_pre bits)
|--
  “ ((r + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (r + 1)) ”

noncomputable def solver_safety_wit_8 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (r : Int) (PreH1 : (((r + 1) * (r + 1)) > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH6 : (Pre bits)) (PreH7 : ((0 : Int) <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r) <= n_pre)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** (charArray.full s_pre n_pre bits)
|--
  “ ((r * r) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (r * r)) ”

noncomputable def solver_safety_wit_9 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (r : Int) (PreH1 : ((r * r) ≠ n_pre)) (PreH2 : (((r + 1) * (r + 1)) > n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (bits)) = n_pre)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH7 : (Pre bits)) (PreH8 : ((0 : Int) <= r)) (PreH9 : (r <= 447)) (PreH10 : ((r * r) <= n_pre)) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** (charArray.full s_pre n_pre bits)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_10 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (r : Int) (PreH1 : ((r * r) = n_pre)) (PreH2 : (((r + 1) * (r + 1)) > n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (bits)) = n_pre)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH7 : (Pre bits)) (PreH8 : ((0 : Int) <= r)) (PreH9 : (r <= 447)) (PreH10 : ((r * r) <= n_pre)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** (charArray.full s_pre n_pre bits)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_11 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (i : Int) (r : Int) (PreH1 : (i < r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH6 : (Pre bits)) (PreH7 : (1 <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= r)) (PreH12 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (charArray.full s_pre n_pre bits)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_12 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : (j < r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH6 : (Pre bits)) (PreH7 : (1 <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < r)) (PreH12 : ((0 : Int) <= j)) (PreH13 : (j <= r)) (PreH14 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH15 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  ((( &( "border" ) )) # Int |->_)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (charArray.full s_pre n_pre bits)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_13 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : (i ≠ (0 : Int))) (PreH2 : (j < r)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (bits)) = n_pre)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH7 : (Pre bits)) (PreH8 : (1 <= r)) (PreH9 : (r <= 447)) (PreH10 : ((r * r) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < r)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= r)) (PreH15 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH16 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  ((( &( "border" ) )) # Int |->_)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (charArray.full s_pre n_pre bits)
|--
  “ ((r - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (r - 1)) ”

noncomputable def solver_safety_wit_14 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : (i ≠ (0 : Int))) (PreH2 : (j < r)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (bits)) = n_pre)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH7 : (Pre bits)) (PreH8 : (1 <= r)) (PreH9 : (r <= 447)) (PreH10 : ((r * r) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < r)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= r)) (PreH15 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH16 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  ((( &( "border" ) )) # Int |->_)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (charArray.full s_pre n_pre bits)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_15 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : (i ≠ (r - 1))) (PreH2 : (i ≠ (0 : Int))) (PreH3 : (j < r)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (bits)) = n_pre)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH8 : (Pre bits)) (PreH9 : (1 <= r)) (PreH10 : (r <= 447)) (PreH11 : ((r * r) = n_pre)) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < r)) (PreH14 : ((0 : Int) <= j)) (PreH15 : (j <= r)) (PreH16 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH17 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  ((( &( "border" ) )) # Int |->_)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (charArray.full s_pre n_pre bits)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_16 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : (j ≠ (0 : Int))) (PreH2 : (i ≠ (r - 1))) (PreH3 : (i ≠ (0 : Int))) (PreH4 : (j < r)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : ((Zlength (bits)) = n_pre)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH9 : (Pre bits)) (PreH10 : (1 <= r)) (PreH11 : (r <= 447)) (PreH12 : ((r * r) = n_pre)) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < r)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= r)) (PreH17 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH18 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  ((( &( "border" ) )) # Int |->_)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (charArray.full s_pre n_pre bits)
|--
  “ ((r - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (r - 1)) ”

noncomputable def solver_safety_wit_17 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : (j ≠ (0 : Int))) (PreH2 : (i ≠ (r - 1))) (PreH3 : (i ≠ (0 : Int))) (PreH4 : (j < r)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : ((Zlength (bits)) = n_pre)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH9 : (Pre bits)) (PreH10 : (1 <= r)) (PreH11 : (r <= 447)) (PreH12 : ((r * r) = n_pre)) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < r)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= r)) (PreH17 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH18 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  ((( &( "border" ) )) # Int |->_)
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (charArray.full s_pre n_pre bits)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_18 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : (j = (0 : Int))) (PreH2 : (i ≠ (r - 1))) (PreH3 : (i ≠ (0 : Int))) (PreH4 : (j < r)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : ((Zlength (bits)) = n_pre)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH9 : (Pre bits)) (PreH10 : (1 <= r)) (PreH11 : (r <= 447)) (PreH12 : ((r * r) = n_pre)) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < r)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= r)) (PreH17 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH18 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  ((( &( "want" ) )) # Char |->_)
  ** ((( &( "border" ) )) # Int |-> (1))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (charArray.full s_pre n_pre bits)
|--
  “ (49 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 49) ”

noncomputable def solver_safety_wit_19 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : (i = (0 : Int))) (PreH2 : (j < r)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (bits)) = n_pre)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH7 : (Pre bits)) (PreH8 : (1 <= r)) (PreH9 : (r <= 447)) (PreH10 : ((r * r) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < r)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= r)) (PreH15 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH16 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  ((( &( "want" ) )) # Char |->_)
  ** ((( &( "border" ) )) # Int |-> (1))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (charArray.full s_pre n_pre bits)
|--
  “ (49 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 49) ”

noncomputable def solver_safety_wit_20 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : (i = (r - 1))) (PreH2 : (i ≠ (0 : Int))) (PreH3 : (j < r)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (bits)) = n_pre)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH8 : (Pre bits)) (PreH9 : (1 <= r)) (PreH10 : (r <= 447)) (PreH11 : ((r * r) = n_pre)) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < r)) (PreH14 : ((0 : Int) <= j)) (PreH15 : (j <= r)) (PreH16 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH17 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  ((( &( "want" ) )) # Char |->_)
  ** ((( &( "border" ) )) # Int |-> (1))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (charArray.full s_pre n_pre bits)
|--
  “ (49 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 49) ”

noncomputable def solver_safety_wit_21 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : (j = (r - 1))) (PreH2 : (j ≠ (0 : Int))) (PreH3 : (i ≠ (r - 1))) (PreH4 : (i ≠ (0 : Int))) (PreH5 : (j < r)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : ((Zlength (bits)) = n_pre)) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH10 : (Pre bits)) (PreH11 : (1 <= r)) (PreH12 : (r <= 447)) (PreH13 : ((r * r) = n_pre)) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < r)) (PreH16 : ((0 : Int) <= j)) (PreH17 : (j <= r)) (PreH18 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH19 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  ((( &( "want" ) )) # Char |->_)
  ** ((( &( "border" ) )) # Int |-> (1))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (charArray.full s_pre n_pre bits)
|--
  “ (49 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 49) ”

noncomputable def solver_safety_wit_22 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : (j ≠ (r - 1))) (PreH2 : (j ≠ (0 : Int))) (PreH3 : (i ≠ (r - 1))) (PreH4 : (i ≠ (0 : Int))) (PreH5 : (j < r)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : ((Zlength (bits)) = n_pre)) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH10 : (Pre bits)) (PreH11 : (1 <= r)) (PreH12 : (r <= 447)) (PreH13 : ((r * r) = n_pre)) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < r)) (PreH16 : ((0 : Int) <= j)) (PreH17 : (j <= r)) (PreH18 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH19 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  ((( &( "want" ) )) # Char |->_)
  ** ((( &( "border" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (charArray.full s_pre n_pre bits)
|--
  “ (48 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 48) ”

noncomputable def solver_safety_wit_23 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((0 : Int) <= ((i * r) + j))) (PreH2 : (((i * r) + j) < n_pre)) (PreH3 : ((0 : Int) <= INT_MAX)) (PreH4 : ((0 : Int) >= INT_MIN)) (PreH5 : (j ≠ (r - 1))) (PreH6 : (j ≠ (0 : Int))) (PreH7 : (i ≠ (r - 1))) (PreH8 : (i ≠ (0 : Int))) (PreH9 : (j < r)) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 200000)) (PreH12 : ((Zlength (bits)) = n_pre)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH14 : (Pre bits)) (PreH15 : (1 <= r)) (PreH16 : (r <= 447)) (PreH17 : ((r * r) = n_pre)) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i < r)) (PreH20 : ((0 : Int) <= j)) (PreH21 : (j <= r)) (PreH22 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH23 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "want" ) )) # Char |-> (48))
  ** ((( &( "border" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.full s_pre n_pre bits)
|--
  “ (((i * r) + j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((i * r) + j)) ”

noncomputable def solver_safety_wit_24 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((0 : Int) <= ((i * r) + j))) (PreH2 : (((i * r) + j) < n_pre)) (PreH3 : (1 <= INT_MAX)) (PreH4 : (1 >= INT_MIN)) (PreH5 : (j = (r - 1))) (PreH6 : (j ≠ (0 : Int))) (PreH7 : (i ≠ (r - 1))) (PreH8 : (i ≠ (0 : Int))) (PreH9 : (j < r)) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 200000)) (PreH12 : ((Zlength (bits)) = n_pre)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH14 : (Pre bits)) (PreH15 : (1 <= r)) (PreH16 : (r <= 447)) (PreH17 : ((r * r) = n_pre)) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i < r)) (PreH20 : ((0 : Int) <= j)) (PreH21 : (j <= r)) (PreH22 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH23 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "want" ) )) # Char |-> (49))
  ** ((( &( "border" ) )) # Int |-> (1))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.full s_pre n_pre bits)
|--
  “ (((i * r) + j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((i * r) + j)) ”

noncomputable def solver_safety_wit_25 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((0 : Int) <= ((i * r) + j))) (PreH2 : (((i * r) + j) < n_pre)) (PreH3 : (1 <= INT_MAX)) (PreH4 : (1 >= INT_MIN)) (PreH5 : (i = (r - 1))) (PreH6 : (i ≠ (0 : Int))) (PreH7 : (j < r)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : ((Zlength (bits)) = n_pre)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH12 : (Pre bits)) (PreH13 : (1 <= r)) (PreH14 : (r <= 447)) (PreH15 : ((r * r) = n_pre)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < r)) (PreH18 : ((0 : Int) <= j)) (PreH19 : (j <= r)) (PreH20 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH21 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "want" ) )) # Char |-> (49))
  ** ((( &( "border" ) )) # Int |-> (1))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.full s_pre n_pre bits)
|--
  “ (((i * r) + j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((i * r) + j)) ”

noncomputable def solver_safety_wit_26 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((0 : Int) <= ((i * r) + j))) (PreH2 : (((i * r) + j) < n_pre)) (PreH3 : (1 <= INT_MAX)) (PreH4 : (1 >= INT_MIN)) (PreH5 : (i = (0 : Int))) (PreH6 : (j < r)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((Zlength (bits)) = n_pre)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH11 : (Pre bits)) (PreH12 : (1 <= r)) (PreH13 : (r <= 447)) (PreH14 : ((r * r) = n_pre)) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i < r)) (PreH17 : ((0 : Int) <= j)) (PreH18 : (j <= r)) (PreH19 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH20 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "want" ) )) # Char |-> (49))
  ** ((( &( "border" ) )) # Int |-> (1))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.full s_pre n_pre bits)
|--
  “ (((i * r) + j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((i * r) + j)) ”

noncomputable def solver_safety_wit_27 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((0 : Int) <= ((i * r) + j))) (PreH2 : (((i * r) + j) < n_pre)) (PreH3 : (1 <= INT_MAX)) (PreH4 : (1 >= INT_MIN)) (PreH5 : (j = (0 : Int))) (PreH6 : (i ≠ (r - 1))) (PreH7 : (i ≠ (0 : Int))) (PreH8 : (j < r)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : ((Zlength (bits)) = n_pre)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH13 : (Pre bits)) (PreH14 : (1 <= r)) (PreH15 : (r <= 447)) (PreH16 : ((r * r) = n_pre)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < r)) (PreH19 : ((0 : Int) <= j)) (PreH20 : (j <= r)) (PreH21 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH22 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "want" ) )) # Char |-> (49))
  ** ((( &( "border" ) )) # Int |-> (1))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.full s_pre n_pre bits)
|--
  “ (((i * r) + j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((i * r) + j)) ”

noncomputable def solver_safety_wit_28 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((0 : Int) <= ((i * r) + j))) (PreH2 : (((i * r) + j) < n_pre)) (PreH3 : ((0 : Int) <= INT_MAX)) (PreH4 : ((0 : Int) >= INT_MIN)) (PreH5 : (j ≠ (r - 1))) (PreH6 : (j ≠ (0 : Int))) (PreH7 : (i ≠ (r - 1))) (PreH8 : (i ≠ (0 : Int))) (PreH9 : (j < r)) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 200000)) (PreH12 : ((Zlength (bits)) = n_pre)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH14 : (Pre bits)) (PreH15 : (1 <= r)) (PreH16 : (r <= 447)) (PreH17 : ((r * r) = n_pre)) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i < r)) (PreH20 : ((0 : Int) <= j)) (PreH21 : (j <= r)) (PreH22 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH23 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "want" ) )) # Char |-> (48))
  ** ((( &( "border" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.full s_pre n_pre bits)
|--
  “ ((i * r) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i * r)) ”

noncomputable def solver_safety_wit_29 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((0 : Int) <= ((i * r) + j))) (PreH2 : (((i * r) + j) < n_pre)) (PreH3 : (1 <= INT_MAX)) (PreH4 : (1 >= INT_MIN)) (PreH5 : (j = (r - 1))) (PreH6 : (j ≠ (0 : Int))) (PreH7 : (i ≠ (r - 1))) (PreH8 : (i ≠ (0 : Int))) (PreH9 : (j < r)) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 200000)) (PreH12 : ((Zlength (bits)) = n_pre)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH14 : (Pre bits)) (PreH15 : (1 <= r)) (PreH16 : (r <= 447)) (PreH17 : ((r * r) = n_pre)) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i < r)) (PreH20 : ((0 : Int) <= j)) (PreH21 : (j <= r)) (PreH22 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH23 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "want" ) )) # Char |-> (49))
  ** ((( &( "border" ) )) # Int |-> (1))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.full s_pre n_pre bits)
|--
  “ ((i * r) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i * r)) ”

noncomputable def solver_safety_wit_30 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((0 : Int) <= ((i * r) + j))) (PreH2 : (((i * r) + j) < n_pre)) (PreH3 : (1 <= INT_MAX)) (PreH4 : (1 >= INT_MIN)) (PreH5 : (i = (r - 1))) (PreH6 : (i ≠ (0 : Int))) (PreH7 : (j < r)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : ((Zlength (bits)) = n_pre)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH12 : (Pre bits)) (PreH13 : (1 <= r)) (PreH14 : (r <= 447)) (PreH15 : ((r * r) = n_pre)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < r)) (PreH18 : ((0 : Int) <= j)) (PreH19 : (j <= r)) (PreH20 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH21 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "want" ) )) # Char |-> (49))
  ** ((( &( "border" ) )) # Int |-> (1))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.full s_pre n_pre bits)
|--
  “ ((i * r) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i * r)) ”

noncomputable def solver_safety_wit_31 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((0 : Int) <= ((i * r) + j))) (PreH2 : (((i * r) + j) < n_pre)) (PreH3 : (1 <= INT_MAX)) (PreH4 : (1 >= INT_MIN)) (PreH5 : (i = (0 : Int))) (PreH6 : (j < r)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((Zlength (bits)) = n_pre)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH11 : (Pre bits)) (PreH12 : (1 <= r)) (PreH13 : (r <= 447)) (PreH14 : ((r * r) = n_pre)) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i < r)) (PreH17 : ((0 : Int) <= j)) (PreH18 : (j <= r)) (PreH19 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH20 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "want" ) )) # Char |-> (49))
  ** ((( &( "border" ) )) # Int |-> (1))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.full s_pre n_pre bits)
|--
  “ ((i * r) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i * r)) ”

noncomputable def solver_safety_wit_32 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((0 : Int) <= ((i * r) + j))) (PreH2 : (((i * r) + j) < n_pre)) (PreH3 : (1 <= INT_MAX)) (PreH4 : (1 >= INT_MIN)) (PreH5 : (j = (0 : Int))) (PreH6 : (i ≠ (r - 1))) (PreH7 : (i ≠ (0 : Int))) (PreH8 : (j < r)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : ((Zlength (bits)) = n_pre)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH13 : (Pre bits)) (PreH14 : (1 <= r)) (PreH15 : (r <= 447)) (PreH16 : ((r * r) = n_pre)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < r)) (PreH19 : ((0 : Int) <= j)) (PreH20 : (j <= r)) (PreH21 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH22 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "want" ) )) # Char |-> (49))
  ** ((( &( "border" ) )) # Int |-> (1))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.full s_pre n_pre bits)
|--
  “ ((i * r) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i * r)) ”

noncomputable def solver_safety_wit_33 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((Znth ((i * r) + j) bits (0 : Int)) ≠ 49)) (PreH2 : ((0 : Int) <= ((i * r) + j))) (PreH3 : (((i * r) + j) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (j = (0 : Int))) (PreH7 : (i ≠ (r - 1))) (PreH8 : (i ≠ (0 : Int))) (PreH9 : (j < r)) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 200000)) (PreH12 : ((Zlength (bits)) = n_pre)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH14 : (Pre bits)) (PreH15 : (1 <= r)) (PreH16 : (r <= 447)) (PreH17 : ((r * r) = n_pre)) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i < r)) (PreH20 : ((0 : Int) <= j)) (PreH21 : (j <= r)) (PreH22 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH23 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  (charArray.full s_pre n_pre bits)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "want" ) )) # Char |-> (49))
  ** ((( &( "border" ) )) # Int |-> (1))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_34 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((Znth ((i * r) + j) bits (0 : Int)) ≠ 49)) (PreH2 : ((0 : Int) <= ((i * r) + j))) (PreH3 : (((i * r) + j) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (i = (0 : Int))) (PreH7 : (j < r)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : ((Zlength (bits)) = n_pre)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH12 : (Pre bits)) (PreH13 : (1 <= r)) (PreH14 : (r <= 447)) (PreH15 : ((r * r) = n_pre)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < r)) (PreH18 : ((0 : Int) <= j)) (PreH19 : (j <= r)) (PreH20 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH21 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  (charArray.full s_pre n_pre bits)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "want" ) )) # Char |-> (49))
  ** ((( &( "border" ) )) # Int |-> (1))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_35 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((Znth ((i * r) + j) bits (0 : Int)) ≠ 49)) (PreH2 : ((0 : Int) <= ((i * r) + j))) (PreH3 : (((i * r) + j) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (i = (r - 1))) (PreH7 : (i ≠ (0 : Int))) (PreH8 : (j < r)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : ((Zlength (bits)) = n_pre)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH13 : (Pre bits)) (PreH14 : (1 <= r)) (PreH15 : (r <= 447)) (PreH16 : ((r * r) = n_pre)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < r)) (PreH19 : ((0 : Int) <= j)) (PreH20 : (j <= r)) (PreH21 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH22 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  (charArray.full s_pre n_pre bits)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "want" ) )) # Char |-> (49))
  ** ((( &( "border" ) )) # Int |-> (1))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_36 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((Znth ((i * r) + j) bits (0 : Int)) ≠ 49)) (PreH2 : ((0 : Int) <= ((i * r) + j))) (PreH3 : (((i * r) + j) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (j = (r - 1))) (PreH7 : (j ≠ (0 : Int))) (PreH8 : (i ≠ (r - 1))) (PreH9 : (i ≠ (0 : Int))) (PreH10 : (j < r)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((Zlength (bits)) = n_pre)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH15 : (Pre bits)) (PreH16 : (1 <= r)) (PreH17 : (r <= 447)) (PreH18 : ((r * r) = n_pre)) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i < r)) (PreH21 : ((0 : Int) <= j)) (PreH22 : (j <= r)) (PreH23 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH24 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  (charArray.full s_pre n_pre bits)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "want" ) )) # Char |-> (49))
  ** ((( &( "border" ) )) # Int |-> (1))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_37 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((Znth ((i * r) + j) bits (0 : Int)) ≠ 48)) (PreH2 : ((0 : Int) <= ((i * r) + j))) (PreH3 : (((i * r) + j) < n_pre)) (PreH4 : ((0 : Int) <= INT_MAX)) (PreH5 : ((0 : Int) >= INT_MIN)) (PreH6 : (j ≠ (r - 1))) (PreH7 : (j ≠ (0 : Int))) (PreH8 : (i ≠ (r - 1))) (PreH9 : (i ≠ (0 : Int))) (PreH10 : (j < r)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((Zlength (bits)) = n_pre)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH15 : (Pre bits)) (PreH16 : (1 <= r)) (PreH17 : (r <= 447)) (PreH18 : ((r * r) = n_pre)) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i < r)) (PreH21 : ((0 : Int) <= j)) (PreH22 : (j <= r)) (PreH23 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH24 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  (charArray.full s_pre n_pre bits)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "want" ) )) # Char |-> (48))
  ** ((( &( "border" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_38 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : (j >= r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH6 : (Pre bits)) (PreH7 : (1 <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < r)) (PreH12 : ((0 : Int) <= j)) (PreH13 : (j <= r)) (PreH14 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH15 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (charArray.full s_pre n_pre bits)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_39 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((Znth ((i * r) + j) bits (0 : Int)) = 49)) (PreH2 : ((0 : Int) <= ((i * r) + j))) (PreH3 : (((i * r) + j) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (j = (0 : Int))) (PreH7 : (i ≠ (r - 1))) (PreH8 : (i ≠ (0 : Int))) (PreH9 : (j < r)) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 200000)) (PreH12 : ((Zlength (bits)) = n_pre)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH14 : (Pre bits)) (PreH15 : (1 <= r)) (PreH16 : (r <= 447)) (PreH17 : ((r * r) = n_pre)) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i < r)) (PreH20 : ((0 : Int) <= j)) (PreH21 : (j <= r)) (PreH22 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH23 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  (charArray.full s_pre n_pre bits)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def solver_safety_wit_40 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((Znth ((i * r) + j) bits (0 : Int)) = 49)) (PreH2 : ((0 : Int) <= ((i * r) + j))) (PreH3 : (((i * r) + j) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (i = (0 : Int))) (PreH7 : (j < r)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : ((Zlength (bits)) = n_pre)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH12 : (Pre bits)) (PreH13 : (1 <= r)) (PreH14 : (r <= 447)) (PreH15 : ((r * r) = n_pre)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < r)) (PreH18 : ((0 : Int) <= j)) (PreH19 : (j <= r)) (PreH20 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH21 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  (charArray.full s_pre n_pre bits)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def solver_safety_wit_41 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((Znth ((i * r) + j) bits (0 : Int)) = 49)) (PreH2 : ((0 : Int) <= ((i * r) + j))) (PreH3 : (((i * r) + j) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (i = (r - 1))) (PreH7 : (i ≠ (0 : Int))) (PreH8 : (j < r)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : ((Zlength (bits)) = n_pre)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH13 : (Pre bits)) (PreH14 : (1 <= r)) (PreH15 : (r <= 447)) (PreH16 : ((r * r) = n_pre)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < r)) (PreH19 : ((0 : Int) <= j)) (PreH20 : (j <= r)) (PreH21 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH22 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  (charArray.full s_pre n_pre bits)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def solver_safety_wit_42 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((Znth ((i * r) + j) bits (0 : Int)) = 49)) (PreH2 : ((0 : Int) <= ((i * r) + j))) (PreH3 : (((i * r) + j) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (j = (r - 1))) (PreH7 : (j ≠ (0 : Int))) (PreH8 : (i ≠ (r - 1))) (PreH9 : (i ≠ (0 : Int))) (PreH10 : (j < r)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((Zlength (bits)) = n_pre)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH15 : (Pre bits)) (PreH16 : (1 <= r)) (PreH17 : (r <= 447)) (PreH18 : ((r * r) = n_pre)) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i < r)) (PreH21 : ((0 : Int) <= j)) (PreH22 : (j <= r)) (PreH23 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH24 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  (charArray.full s_pre n_pre bits)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def solver_safety_wit_43 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((Znth ((i * r) + j) bits (0 : Int)) = 48)) (PreH2 : ((0 : Int) <= ((i * r) + j))) (PreH3 : (((i * r) + j) < n_pre)) (PreH4 : ((0 : Int) <= INT_MAX)) (PreH5 : ((0 : Int) >= INT_MIN)) (PreH6 : (j ≠ (r - 1))) (PreH7 : (j ≠ (0 : Int))) (PreH8 : (i ≠ (r - 1))) (PreH9 : (i ≠ (0 : Int))) (PreH10 : (j < r)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((Zlength (bits)) = n_pre)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH15 : (Pre bits)) (PreH16 : (1 <= r)) (PreH17 : (r <= 447)) (PreH18 : ((r * r) = n_pre)) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i < r)) (PreH21 : ((0 : Int) <= j)) (PreH22 : (j <= r)) (PreH23 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH24 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  (charArray.full s_pre n_pre bits)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def solver_safety_wit_44 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (i : Int) (r : Int) (PreH1 : (i >= r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH6 : (Pre bits)) (PreH7 : (1 <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= r)) (PreH12 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) ,
  ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** (charArray.full s_pre n_pre bits)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((Zlength (bits)) = n_pre)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((Znth i bits (0 : Int)) = 48) ∨ ((Znth i bits (0 : Int)) = 49)))) (PreH5 : (Pre bits)) ,
  (charArray.full s_pre n_pre bits)
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((Zlength (bits)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49))) ” &&
  “ (Pre bits) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 447) ” &&
  “ (((0 : Int) * (0 : Int)) <= n_pre) ”
  &&  (charArray.full s_pre n_pre bits)
) \/
(
forall (bits : (List Int)) (n_pre : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((Zlength (bits)) = n_pre)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((Znth i bits (0 : Int)) = 48) ∨ ((Znth i bits (0 : Int)) = 49)))) (PreH5 : (Pre bits)) ,
  TT && emp 
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49))) ”
  &&  emp
)

noncomputable def solver_entail_wit_1_split_goal_1 : Prop :=
  forall (bits : (List Int)) (n_pre : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((Zlength (bits)) = n_pre)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((Znth i bits (0 : Int)) = 48) ∨ ((Znth i bits (0 : Int)) = 49)))) (PreH5 : (Pre bits)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))

noncomputable def solver_entail_wit_2 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (r : Int) (PreH1 : (((r + 1) * (r + 1)) <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH6 : (Pre bits)) (PreH7 : ((0 : Int) <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r) <= n_pre)) ,
  (charArray.full s_pre n_pre bits)
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((Zlength (bits)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49))) ” &&
  “ (Pre bits) ” &&
  “ ((0 : Int) <= (r + 1)) ” &&
  “ ((r + 1) <= 447) ” &&
  “ (((r + 1) * (r + 1)) <= n_pre) ”
  &&  (charArray.full s_pre n_pre bits)

noncomputable def solver_entail_wit_3 : Prop :=
  (
forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (r : Int) (PreH1 : ((r * r) = n_pre)) (PreH2 : (((r + 1) * (r + 1)) > n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (bits)) = n_pre)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((Znth k_2 bits (0 : Int)) = 48) ∨ ((Znth k_2 bits (0 : Int)) = 49)))) (PreH7 : (Pre bits)) (PreH8 : ((0 : Int) <= r)) (PreH9 : (r <= 447)) (PreH10 : ((r * r) <= n_pre)) ,
  (charArray.full s_pre n_pre bits)
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((Zlength (bits)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49))) ” &&
  “ (Pre bits) ” &&
  “ (1 <= r) ” &&
  “ (r <= 447) ” &&
  “ ((r * r) = n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= r) ” &&
  “ forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < (0 : Int))) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48)))) ”
  &&  (charArray.full s_pre n_pre bits)
) \/
(
forall (bits : (List Int)) (n_pre : Int) (r : Int) (PreH1 : ((r * r) = n_pre)) (PreH2 : (((r + 1) * (r + 1)) > n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (bits)) = n_pre)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((Znth k_2 bits (0 : Int)) = 48) ∨ ((Znth k_2 bits (0 : Int)) = 49)))) (PreH7 : (Pre bits)) (PreH8 : ((0 : Int) <= r)) (PreH9 : (r <= 447)) (PreH10 : ((r * r) <= n_pre)) ,
  TT && emp 
|--
  “ forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < (0 : Int))) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48)))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49))) ”
  &&  emp
)

noncomputable def solver_entail_wit_3_split_goal_1 : Prop :=
  forall (bits : (List Int)) (n_pre : Int) (r : Int) (PreH1 : ((r * r) = n_pre)) (PreH2 : (((r + 1) * (r + 1)) > n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (bits)) = n_pre)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((Znth k_2 bits (0 : Int)) = 48) ∨ ((Znth k_2 bits (0 : Int)) = 49)))) (PreH7 : (Pre bits)) (PreH8 : ((0 : Int) <= r)) (PreH9 : (r <= 447)) (PreH10 : ((r * r) <= n_pre)) ,
  forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < (0 : Int))) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))

noncomputable def solver_entail_wit_3_split_goal_2 : Prop :=
  forall (bits : (List Int)) (n_pre : Int) (r : Int) (PreH1 : ((r * r) = n_pre)) (PreH2 : (((r + 1) * (r + 1)) > n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (bits)) = n_pre)) (PreH6 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((Znth k_2 bits (0 : Int)) = 48) ∨ ((Znth k_2 bits (0 : Int)) = 49)))) (PreH7 : (Pre bits)) (PreH8 : ((0 : Int) <= r)) (PreH9 : (r <= 447)) (PreH10 : ((r * r) <= n_pre)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))

noncomputable def solver_entail_wit_4 : Prop :=
  (
forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (i : Int) (r : Int) (PreH1 : (i < r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((Znth k_2 bits (0 : Int)) = 48) ∨ ((Znth k_2 bits (0 : Int)) = 49)))) (PreH6 : (Pre bits)) (PreH7 : (1 <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= r)) (PreH12 : forall (x_2 : Int) , forall (y_3 : Int) , ((((((0 : Int) <= x_2) ∧ (x_2 < i)) ∧ ((0 : Int) <= y_3)) ∧ (y_3 < r)) -> ((((((x_2 = (0 : Int)) ∨ (x_2 = (r - 1))) ∨ (y_3 = (0 : Int))) ∨ (y_3 = (r - 1))) ∧ ((Znth ((x_2 * r) + y_3) bits (0 : Int)) = 49)) ∨ (((((x_2 ≠ (0 : Int)) ∧ (x_2 ≠ (r - 1))) ∧ (y_3 ≠ (0 : Int))) ∧ (y_3 ≠ (r - 1))) ∧ ((Znth ((x_2 * r) + y_3) bits (0 : Int)) = 48))))) ,
  (charArray.full s_pre n_pre bits)
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((Zlength (bits)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49))) ” &&
  “ (Pre bits) ” &&
  “ (1 <= r) ” &&
  “ (r <= 447) ” &&
  “ ((r * r) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < r) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= r) ” &&
  “ forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48)))) ” &&
  “ forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < (0 : Int))) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48)))) ”
  &&  (charArray.full s_pre n_pre bits)
) \/
(
forall (bits : (List Int)) (n_pre : Int) (i : Int) (r : Int) (PreH1 : (i < r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((Znth k_2 bits (0 : Int)) = 48) ∨ ((Znth k_2 bits (0 : Int)) = 49)))) (PreH6 : (Pre bits)) (PreH7 : (1 <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= r)) (PreH12 : forall (x_2 : Int) , forall (y_3 : Int) , ((((((0 : Int) <= x_2) ∧ (x_2 < i)) ∧ ((0 : Int) <= y_3)) ∧ (y_3 < r)) -> ((((((x_2 = (0 : Int)) ∨ (x_2 = (r - 1))) ∨ (y_3 = (0 : Int))) ∨ (y_3 = (r - 1))) ∧ ((Znth ((x_2 * r) + y_3) bits (0 : Int)) = 49)) ∨ (((((x_2 ≠ (0 : Int)) ∧ (x_2 ≠ (r - 1))) ∧ (y_3 ≠ (0 : Int))) ∧ (y_3 ≠ (r - 1))) ∧ ((Znth ((x_2 * r) + y_3) bits (0 : Int)) = 48))))) ,
  TT && emp 
|--
  “ forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < (0 : Int))) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48)))) ” &&
  “ forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48)))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49))) ”
  &&  emp
)

noncomputable def solver_entail_wit_4_split_goal_1 : Prop :=
  forall (bits : (List Int)) (n_pre : Int) (i : Int) (r : Int) (PreH1 : (i < r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((Znth k_2 bits (0 : Int)) = 48) ∨ ((Znth k_2 bits (0 : Int)) = 49)))) (PreH6 : (Pre bits)) (PreH7 : (1 <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= r)) (PreH12 : forall (x_2 : Int) , forall (y_3 : Int) , ((((((0 : Int) <= x_2) ∧ (x_2 < i)) ∧ ((0 : Int) <= y_3)) ∧ (y_3 < r)) -> ((((((x_2 = (0 : Int)) ∨ (x_2 = (r - 1))) ∨ (y_3 = (0 : Int))) ∨ (y_3 = (r - 1))) ∧ ((Znth ((x_2 * r) + y_3) bits (0 : Int)) = 49)) ∨ (((((x_2 ≠ (0 : Int)) ∧ (x_2 ≠ (r - 1))) ∧ (y_3 ≠ (0 : Int))) ∧ (y_3 ≠ (r - 1))) ∧ ((Znth ((x_2 * r) + y_3) bits (0 : Int)) = 48))))) ,
  forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < (0 : Int))) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))

noncomputable def solver_entail_wit_4_split_goal_2 : Prop :=
  forall (bits : (List Int)) (n_pre : Int) (i : Int) (r : Int) (PreH1 : (i < r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((Znth k_2 bits (0 : Int)) = 48) ∨ ((Znth k_2 bits (0 : Int)) = 49)))) (PreH6 : (Pre bits)) (PreH7 : (1 <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= r)) (PreH12 : forall (x_2 : Int) , forall (y_3 : Int) , ((((((0 : Int) <= x_2) ∧ (x_2 < i)) ∧ ((0 : Int) <= y_3)) ∧ (y_3 < r)) -> ((((((x_2 = (0 : Int)) ∨ (x_2 = (r - 1))) ∨ (y_3 = (0 : Int))) ∨ (y_3 = (r - 1))) ∧ ((Znth ((x_2 * r) + y_3) bits (0 : Int)) = 49)) ∨ (((((x_2 ≠ (0 : Int)) ∧ (x_2 ≠ (r - 1))) ∧ (y_3 ≠ (0 : Int))) ∧ (y_3 ≠ (r - 1))) ∧ ((Znth ((x_2 * r) + y_3) bits (0 : Int)) = 48))))) ,
  forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))

noncomputable def solver_entail_wit_4_split_goal_3 : Prop :=
  forall (bits : (List Int)) (n_pre : Int) (i : Int) (r : Int) (PreH1 : (i < r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((Znth k_2 bits (0 : Int)) = 48) ∨ ((Znth k_2 bits (0 : Int)) = 49)))) (PreH6 : (Pre bits)) (PreH7 : (1 <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= r)) (PreH12 : forall (x_2 : Int) , forall (y_3 : Int) , ((((((0 : Int) <= x_2) ∧ (x_2 < i)) ∧ ((0 : Int) <= y_3)) ∧ (y_3 < r)) -> ((((((x_2 = (0 : Int)) ∨ (x_2 = (r - 1))) ∨ (y_3 = (0 : Int))) ∨ (y_3 = (r - 1))) ∧ ((Znth ((x_2 * r) + y_3) bits (0 : Int)) = 49)) ∨ (((((x_2 ≠ (0 : Int)) ∧ (x_2 ≠ (r - 1))) ∧ (y_3 ≠ (0 : Int))) ∧ (y_3 ≠ (r - 1))) ∧ ((Znth ((x_2 * r) + y_3) bits (0 : Int)) = 48))))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))

noncomputable def solver_entail_wit_5_1 : Prop :=
  (
forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : (j = (0 : Int))) (PreH2 : (i ≠ (r - 1))) (PreH3 : (i ≠ (0 : Int))) (PreH4 : (j < r)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : ((Zlength (bits)) = n_pre)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH9 : (Pre bits)) (PreH10 : (1 <= r)) (PreH11 : (r <= 447)) (PreH12 : ((r * r) = n_pre)) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < r)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= r)) (PreH17 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH18 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  ((( &( "want" ) )) # Char |-> (49))
  ** ((( &( "border" ) )) # Int |-> (1))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (charArray.full s_pre n_pre bits)
|--
  “ ((0 : Int) <= ((i * r) + j)) ” &&
  “ (((i * r) + j) < n_pre) ” &&
  “ (1 <= INT_MAX) ” &&
  “ (1 >= INT_MIN) ” &&
  “ (j = (0 : Int)) ” &&
  “ (i ≠ (r - 1)) ” &&
  “ (i ≠ (0 : Int)) ” &&
  “ (j < r) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((Zlength (bits)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49))) ” &&
  “ (Pre bits) ” &&
  “ (1 <= r) ” &&
  “ (r <= 447) ” &&
  “ ((r * r) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < r) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= r) ” &&
  “ forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48)))) ” &&
  “ forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48)))) ”
  &&  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "want" ) )) # Char |-> (49))
  ** ((( &( "border" ) )) # Int |-> (1))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.full s_pre n_pre bits)
) \/
(
forall (bits : (List Int)) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (r <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (1 <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (r >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : (1 >= INT_MIN)) (PreH11 : (j = (0 : Int))) (PreH12 : (i ≠ (r - 1))) (PreH13 : (i ≠ (0 : Int))) (PreH14 : (j < r)) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : ((Zlength (bits)) = n_pre)) (PreH18 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH19 : (Pre bits)) (PreH20 : (1 <= r)) (PreH21 : (r <= 447)) (PreH22 : ((r * r) = n_pre)) (PreH23 : ((0 : Int) <= i)) (PreH24 : (i < r)) (PreH25 : ((0 : Int) <= j)) (PreH26 : (j <= r)) (PreH27 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH28 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  TT && emp 
|--
  “ (((i * r) + (0 : Int)) < (r * r)) ”
  &&  emp
)

noncomputable def solver_entail_wit_5_1_split_goal_1 : Prop :=
  forall (bits : (List Int)) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (r <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (1 <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (r >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : (1 >= INT_MIN)) (PreH11 : (j = (0 : Int))) (PreH12 : (i ≠ (r - 1))) (PreH13 : (i ≠ (0 : Int))) (PreH14 : (j < r)) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : ((Zlength (bits)) = n_pre)) (PreH18 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH19 : (Pre bits)) (PreH20 : (1 <= r)) (PreH21 : (r <= 447)) (PreH22 : ((r * r) = n_pre)) (PreH23 : ((0 : Int) <= i)) (PreH24 : (i < r)) (PreH25 : ((0 : Int) <= j)) (PreH26 : (j <= r)) (PreH27 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH28 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  (((i * r) + (0 : Int)) < (r * r))

noncomputable def solver_entail_wit_5_2 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : (i = (0 : Int))) (PreH2 : (j < r)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (bits)) = n_pre)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH7 : (Pre bits)) (PreH8 : (1 <= r)) (PreH9 : (r <= 447)) (PreH10 : ((r * r) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < r)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= r)) (PreH15 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH16 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  ((( &( "want" ) )) # Char |-> (49))
  ** ((( &( "border" ) )) # Int |-> (1))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (charArray.full s_pre n_pre bits)
|--
  “ ((0 : Int) <= ((i * r) + j)) ” &&
  “ (((i * r) + j) < n_pre) ” &&
  “ (1 <= INT_MAX) ” &&
  “ (1 >= INT_MIN) ” &&
  “ (i = (0 : Int)) ” &&
  “ (j < r) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((Zlength (bits)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49))) ” &&
  “ (Pre bits) ” &&
  “ (1 <= r) ” &&
  “ (r <= 447) ” &&
  “ ((r * r) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < r) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= r) ” &&
  “ forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48)))) ” &&
  “ forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48)))) ”
  &&  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "want" ) )) # Char |-> (49))
  ** ((( &( "border" ) )) # Int |-> (1))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.full s_pre n_pre bits)

noncomputable def solver_entail_wit_5_3 : Prop :=
  (
forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : (i = (r - 1))) (PreH2 : (i ≠ (0 : Int))) (PreH3 : (j < r)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (bits)) = n_pre)) (PreH7 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH8 : (Pre bits)) (PreH9 : (1 <= r)) (PreH10 : (r <= 447)) (PreH11 : ((r * r) = n_pre)) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < r)) (PreH14 : ((0 : Int) <= j)) (PreH15 : (j <= r)) (PreH16 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH17 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  ((( &( "want" ) )) # Char |-> (49))
  ** ((( &( "border" ) )) # Int |-> (1))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (charArray.full s_pre n_pre bits)
|--
  “ ((0 : Int) <= ((i * r) + j)) ” &&
  “ (((i * r) + j) < n_pre) ” &&
  “ (1 <= INT_MAX) ” &&
  “ (1 >= INT_MIN) ” &&
  “ (i = (r - 1)) ” &&
  “ (i ≠ (0 : Int)) ” &&
  “ (j < r) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((Zlength (bits)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49))) ” &&
  “ (Pre bits) ” &&
  “ (1 <= r) ” &&
  “ (r <= 447) ” &&
  “ ((r * r) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < r) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= r) ” &&
  “ forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48)))) ” &&
  “ forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48)))) ”
  &&  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "want" ) )) # Char |-> (49))
  ** ((( &( "border" ) )) # Int |-> (1))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.full s_pre n_pre bits)
) \/
(
forall (bits : (List Int)) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (r <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (1 <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (r >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : (1 >= INT_MIN)) (PreH11 : (i = (r - 1))) (PreH12 : (i ≠ (0 : Int))) (PreH13 : (j < r)) (PreH14 : (2 <= n_pre)) (PreH15 : (n_pre <= 200000)) (PreH16 : ((Zlength (bits)) = n_pre)) (PreH17 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH18 : (Pre bits)) (PreH19 : (1 <= r)) (PreH20 : (r <= 447)) (PreH21 : ((r * r) = n_pre)) (PreH22 : ((0 : Int) <= i)) (PreH23 : (i < r)) (PreH24 : ((0 : Int) <= j)) (PreH25 : (j <= r)) (PreH26 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH27 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  TT && emp 
|--
  “ ((((r - 1) * r) + j) < (r * r)) ”
  &&  emp
)

noncomputable def solver_entail_wit_5_3_split_goal_1 : Prop :=
  forall (bits : (List Int)) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (r <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (1 <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (r >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : (1 >= INT_MIN)) (PreH11 : (i = (r - 1))) (PreH12 : (i ≠ (0 : Int))) (PreH13 : (j < r)) (PreH14 : (2 <= n_pre)) (PreH15 : (n_pre <= 200000)) (PreH16 : ((Zlength (bits)) = n_pre)) (PreH17 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH18 : (Pre bits)) (PreH19 : (1 <= r)) (PreH20 : (r <= 447)) (PreH21 : ((r * r) = n_pre)) (PreH22 : ((0 : Int) <= i)) (PreH23 : (i < r)) (PreH24 : ((0 : Int) <= j)) (PreH25 : (j <= r)) (PreH26 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH27 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  ((((r - 1) * r) + j) < (r * r))

noncomputable def solver_entail_wit_5_4 : Prop :=
  (
forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : (j = (r - 1))) (PreH2 : (j ≠ (0 : Int))) (PreH3 : (i ≠ (r - 1))) (PreH4 : (i ≠ (0 : Int))) (PreH5 : (j < r)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : ((Zlength (bits)) = n_pre)) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH10 : (Pre bits)) (PreH11 : (1 <= r)) (PreH12 : (r <= 447)) (PreH13 : ((r * r) = n_pre)) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < r)) (PreH16 : ((0 : Int) <= j)) (PreH17 : (j <= r)) (PreH18 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH19 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  ((( &( "want" ) )) # Char |-> (49))
  ** ((( &( "border" ) )) # Int |-> (1))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (charArray.full s_pre n_pre bits)
|--
  “ ((0 : Int) <= ((i * r) + j)) ” &&
  “ (((i * r) + j) < n_pre) ” &&
  “ (1 <= INT_MAX) ” &&
  “ (1 >= INT_MIN) ” &&
  “ (j = (r - 1)) ” &&
  “ (j ≠ (0 : Int)) ” &&
  “ (i ≠ (r - 1)) ” &&
  “ (i ≠ (0 : Int)) ” &&
  “ (j < r) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((Zlength (bits)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49))) ” &&
  “ (Pre bits) ” &&
  “ (1 <= r) ” &&
  “ (r <= 447) ” &&
  “ ((r * r) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < r) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= r) ” &&
  “ forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48)))) ” &&
  “ forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48)))) ”
  &&  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "want" ) )) # Char |-> (49))
  ** ((( &( "border" ) )) # Int |-> (1))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.full s_pre n_pre bits)
) \/
(
forall (bits : (List Int)) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (r <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (1 <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (r >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : (1 >= INT_MIN)) (PreH11 : (j = (r - 1))) (PreH12 : (j ≠ (0 : Int))) (PreH13 : (i ≠ (r - 1))) (PreH14 : (i ≠ (0 : Int))) (PreH15 : (j < r)) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 200000)) (PreH18 : ((Zlength (bits)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH20 : (Pre bits)) (PreH21 : (1 <= r)) (PreH22 : (r <= 447)) (PreH23 : ((r * r) = n_pre)) (PreH24 : ((0 : Int) <= i)) (PreH25 : (i < r)) (PreH26 : ((0 : Int) <= j)) (PreH27 : (j <= r)) (PreH28 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH29 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  TT && emp 
|--
  “ (((i * r) + (r - 1)) < (r * r)) ”
  &&  emp
)

noncomputable def solver_entail_wit_5_4_split_goal_1 : Prop :=
  forall (bits : (List Int)) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (r <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (1 <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (r >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : (1 >= INT_MIN)) (PreH11 : (j = (r - 1))) (PreH12 : (j ≠ (0 : Int))) (PreH13 : (i ≠ (r - 1))) (PreH14 : (i ≠ (0 : Int))) (PreH15 : (j < r)) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 200000)) (PreH18 : ((Zlength (bits)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH20 : (Pre bits)) (PreH21 : (1 <= r)) (PreH22 : (r <= 447)) (PreH23 : ((r * r) = n_pre)) (PreH24 : ((0 : Int) <= i)) (PreH25 : (i < r)) (PreH26 : ((0 : Int) <= j)) (PreH27 : (j <= r)) (PreH28 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH29 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  (((i * r) + (r - 1)) < (r * r))

noncomputable def solver_entail_wit_5_5 : Prop :=
  (
forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : (j ≠ (r - 1))) (PreH2 : (j ≠ (0 : Int))) (PreH3 : (i ≠ (r - 1))) (PreH4 : (i ≠ (0 : Int))) (PreH5 : (j < r)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : ((Zlength (bits)) = n_pre)) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH10 : (Pre bits)) (PreH11 : (1 <= r)) (PreH12 : (r <= 447)) (PreH13 : ((r * r) = n_pre)) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < r)) (PreH16 : ((0 : Int) <= j)) (PreH17 : (j <= r)) (PreH18 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH19 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  ((( &( "want" ) )) # Char |-> (48))
  ** ((( &( "border" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (charArray.full s_pre n_pre bits)
|--
  “ ((0 : Int) <= ((i * r) + j)) ” &&
  “ (((i * r) + j) < n_pre) ” &&
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((0 : Int) >= INT_MIN) ” &&
  “ (j ≠ (r - 1)) ” &&
  “ (j ≠ (0 : Int)) ” &&
  “ (i ≠ (r - 1)) ” &&
  “ (i ≠ (0 : Int)) ” &&
  “ (j < r) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((Zlength (bits)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49))) ” &&
  “ (Pre bits) ” &&
  “ (1 <= r) ” &&
  “ (r <= 447) ” &&
  “ ((r * r) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < r) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= r) ” &&
  “ forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48)))) ” &&
  “ forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48)))) ”
  &&  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "want" ) )) # Char |-> (48))
  ** ((( &( "border" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "s" ) )) # Ptr |-> (s_pre))
  ** (charArray.full s_pre n_pre bits)
) \/
(
forall (bits : (List Int)) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (r <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((0 : Int) <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (r >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((0 : Int) >= INT_MIN)) (PreH11 : (j ≠ (r - 1))) (PreH12 : (j ≠ (0 : Int))) (PreH13 : (i ≠ (r - 1))) (PreH14 : (i ≠ (0 : Int))) (PreH15 : (j < r)) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 200000)) (PreH18 : ((Zlength (bits)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH20 : (Pre bits)) (PreH21 : (1 <= r)) (PreH22 : (r <= 447)) (PreH23 : ((r * r) = n_pre)) (PreH24 : ((0 : Int) <= i)) (PreH25 : (i < r)) (PreH26 : ((0 : Int) <= j)) (PreH27 : (j <= r)) (PreH28 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH29 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  TT && emp 
|--
  “ (((i * r) + j) < (r * r)) ”
  &&  emp
)

noncomputable def solver_entail_wit_5_5_split_goal_1 : Prop :=
  forall (bits : (List Int)) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (r <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((0 : Int) <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (r >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((0 : Int) >= INT_MIN)) (PreH11 : (j ≠ (r - 1))) (PreH12 : (j ≠ (0 : Int))) (PreH13 : (i ≠ (r - 1))) (PreH14 : (i ≠ (0 : Int))) (PreH15 : (j < r)) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 200000)) (PreH18 : ((Zlength (bits)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH20 : (Pre bits)) (PreH21 : (1 <= r)) (PreH22 : (r <= 447)) (PreH23 : ((r * r) = n_pre)) (PreH24 : ((0 : Int) <= i)) (PreH25 : (i < r)) (PreH26 : ((0 : Int) <= j)) (PreH27 : (j <= r)) (PreH28 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH29 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  (((i * r) + j) < (r * r))

noncomputable def solver_entail_wit_6 : Prop :=
  (
forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : (j >= r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((Znth k_2 bits (0 : Int)) = 48) ∨ ((Znth k_2 bits (0 : Int)) = 49)))) (PreH6 : (Pre bits)) (PreH7 : (1 <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < r)) (PreH12 : ((0 : Int) <= j)) (PreH13 : (j <= r)) (PreH14 : forall (x_2 : Int) , forall (y_2 : Int) , ((((((0 : Int) <= x_2) ∧ (x_2 < i)) ∧ ((0 : Int) <= y_2)) ∧ (y_2 < r)) -> ((((((x_2 = (0 : Int)) ∨ (x_2 = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((x_2 * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((x_2 ≠ (0 : Int)) ∧ (x_2 ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((x_2 * r) + y_2) bits (0 : Int)) = 48))))) (PreH15 : forall (y_3 : Int) , ((((0 : Int) <= y_3) ∧ (y_3 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_3 = (0 : Int))) ∨ (y_3 = (r - 1))) ∧ ((Znth ((i * r) + y_3) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_3 ≠ (0 : Int))) ∧ (y_3 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_3) bits (0 : Int)) = 48))))) ,
  (charArray.full s_pre n_pre bits)
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((Zlength (bits)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49))) ” &&
  “ (Pre bits) ” &&
  “ (1 <= r) ” &&
  “ (r <= 447) ” &&
  “ ((r * r) = n_pre) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= r) ” &&
  “ forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < (i + 1))) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48)))) ”
  &&  (charArray.full s_pre n_pre bits)
) \/
(
forall (bits : (List Int)) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : (j >= r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((Znth k_2 bits (0 : Int)) = 48) ∨ ((Znth k_2 bits (0 : Int)) = 49)))) (PreH6 : (Pre bits)) (PreH7 : (1 <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < r)) (PreH12 : ((0 : Int) <= j)) (PreH13 : (j <= r)) (PreH14 : forall (x_2 : Int) , forall (y_2 : Int) , ((((((0 : Int) <= x_2) ∧ (x_2 < i)) ∧ ((0 : Int) <= y_2)) ∧ (y_2 < r)) -> ((((((x_2 = (0 : Int)) ∨ (x_2 = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((x_2 * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((x_2 ≠ (0 : Int)) ∧ (x_2 ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((x_2 * r) + y_2) bits (0 : Int)) = 48))))) (PreH15 : forall (y_3 : Int) , ((((0 : Int) <= y_3) ∧ (y_3 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_3 = (0 : Int))) ∨ (y_3 = (r - 1))) ∧ ((Znth ((i * r) + y_3) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_3 ≠ (0 : Int))) ∧ (y_3 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_3) bits (0 : Int)) = 48))))) ,
  TT && emp 
|--
  “ forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < (i + 1))) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48)))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49))) ”
  &&  emp
)

noncomputable def solver_entail_wit_6_split_goal_1 : Prop :=
  forall (bits : (List Int)) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : (j >= r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((Znth k_2 bits (0 : Int)) = 48) ∨ ((Znth k_2 bits (0 : Int)) = 49)))) (PreH6 : (Pre bits)) (PreH7 : (1 <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < r)) (PreH12 : ((0 : Int) <= j)) (PreH13 : (j <= r)) (PreH14 : forall (x_2 : Int) , forall (y_2 : Int) , ((((((0 : Int) <= x_2) ∧ (x_2 < i)) ∧ ((0 : Int) <= y_2)) ∧ (y_2 < r)) -> ((((((x_2 = (0 : Int)) ∨ (x_2 = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((x_2 * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((x_2 ≠ (0 : Int)) ∧ (x_2 ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((x_2 * r) + y_2) bits (0 : Int)) = 48))))) (PreH15 : forall (y_3 : Int) , ((((0 : Int) <= y_3) ∧ (y_3 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_3 = (0 : Int))) ∨ (y_3 = (r - 1))) ∧ ((Znth ((i * r) + y_3) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_3 ≠ (0 : Int))) ∧ (y_3 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_3) bits (0 : Int)) = 48))))) ,
  forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < (i + 1))) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))

noncomputable def solver_entail_wit_6_split_goal_2 : Prop :=
  forall (bits : (List Int)) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : (j >= r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> (((Znth k_2 bits (0 : Int)) = 48) ∨ ((Znth k_2 bits (0 : Int)) = 49)))) (PreH6 : (Pre bits)) (PreH7 : (1 <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < r)) (PreH12 : ((0 : Int) <= j)) (PreH13 : (j <= r)) (PreH14 : forall (x_2 : Int) , forall (y_2 : Int) , ((((((0 : Int) <= x_2) ∧ (x_2 < i)) ∧ ((0 : Int) <= y_2)) ∧ (y_2 < r)) -> ((((((x_2 = (0 : Int)) ∨ (x_2 = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((x_2 * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((x_2 ≠ (0 : Int)) ∧ (x_2 ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((x_2 * r) + y_2) bits (0 : Int)) = 48))))) (PreH15 : forall (y_3 : Int) , ((((0 : Int) <= y_3) ∧ (y_3 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_3 = (0 : Int))) ∨ (y_3 = (r - 1))) ∧ ((Znth ((i * r) + y_3) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_3 ≠ (0 : Int))) ∧ (y_3 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_3) bits (0 : Int)) = 48))))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))

noncomputable def solver_entail_wit_7_1 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((Znth ((i * r) + j) bits (0 : Int)) = 49)) (PreH2 : ((0 : Int) <= ((i * r) + j))) (PreH3 : (((i * r) + j) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (j = (0 : Int))) (PreH7 : (i ≠ (r - 1))) (PreH8 : (i ≠ (0 : Int))) (PreH9 : (j < r)) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 200000)) (PreH12 : ((Zlength (bits)) = n_pre)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH14 : (Pre bits)) (PreH15 : (1 <= r)) (PreH16 : (r <= 447)) (PreH17 : ((r * r) = n_pre)) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i < r)) (PreH20 : ((0 : Int) <= j)) (PreH21 : (j <= r)) (PreH22 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH23 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  (charArray.full s_pre n_pre bits)
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((Zlength (bits)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49))) ” &&
  “ (Pre bits) ” &&
  “ (1 <= r) ” &&
  “ (r <= 447) ” &&
  “ ((r * r) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < r) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= r) ” &&
  “ forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48)))) ” &&
  “ forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < (j + 1))) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48)))) ”
  &&  (charArray.full s_pre n_pre bits)

noncomputable def solver_entail_wit_7_2 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((Znth ((i * r) + j) bits (0 : Int)) = 49)) (PreH2 : ((0 : Int) <= ((i * r) + j))) (PreH3 : (((i * r) + j) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (i = (0 : Int))) (PreH7 : (j < r)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : ((Zlength (bits)) = n_pre)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH12 : (Pre bits)) (PreH13 : (1 <= r)) (PreH14 : (r <= 447)) (PreH15 : ((r * r) = n_pre)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < r)) (PreH18 : ((0 : Int) <= j)) (PreH19 : (j <= r)) (PreH20 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH21 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  (charArray.full s_pre n_pre bits)
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((Zlength (bits)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49))) ” &&
  “ (Pre bits) ” &&
  “ (1 <= r) ” &&
  “ (r <= 447) ” &&
  “ ((r * r) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < r) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= r) ” &&
  “ forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48)))) ” &&
  “ forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < (j + 1))) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48)))) ”
  &&  (charArray.full s_pre n_pre bits)

noncomputable def solver_entail_wit_7_3 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((Znth ((i * r) + j) bits (0 : Int)) = 49)) (PreH2 : ((0 : Int) <= ((i * r) + j))) (PreH3 : (((i * r) + j) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (i = (r - 1))) (PreH7 : (i ≠ (0 : Int))) (PreH8 : (j < r)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : ((Zlength (bits)) = n_pre)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH13 : (Pre bits)) (PreH14 : (1 <= r)) (PreH15 : (r <= 447)) (PreH16 : ((r * r) = n_pre)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < r)) (PreH19 : ((0 : Int) <= j)) (PreH20 : (j <= r)) (PreH21 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH22 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  (charArray.full s_pre n_pre bits)
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((Zlength (bits)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49))) ” &&
  “ (Pre bits) ” &&
  “ (1 <= r) ” &&
  “ (r <= 447) ” &&
  “ ((r * r) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < r) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= r) ” &&
  “ forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48)))) ” &&
  “ forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < (j + 1))) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48)))) ”
  &&  (charArray.full s_pre n_pre bits)

noncomputable def solver_entail_wit_7_4 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((Znth ((i * r) + j) bits (0 : Int)) = 49)) (PreH2 : ((0 : Int) <= ((i * r) + j))) (PreH3 : (((i * r) + j) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (j = (r - 1))) (PreH7 : (j ≠ (0 : Int))) (PreH8 : (i ≠ (r - 1))) (PreH9 : (i ≠ (0 : Int))) (PreH10 : (j < r)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((Zlength (bits)) = n_pre)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH15 : (Pre bits)) (PreH16 : (1 <= r)) (PreH17 : (r <= 447)) (PreH18 : ((r * r) = n_pre)) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i < r)) (PreH21 : ((0 : Int) <= j)) (PreH22 : (j <= r)) (PreH23 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH24 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  (charArray.full s_pre n_pre bits)
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((Zlength (bits)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49))) ” &&
  “ (Pre bits) ” &&
  “ (1 <= r) ” &&
  “ (r <= 447) ” &&
  “ ((r * r) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < r) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= r) ” &&
  “ forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48)))) ” &&
  “ forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < (j + 1))) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48)))) ”
  &&  (charArray.full s_pre n_pre bits)

noncomputable def solver_entail_wit_7_5 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((Znth ((i * r) + j) bits (0 : Int)) = 48)) (PreH2 : ((0 : Int) <= ((i * r) + j))) (PreH3 : (((i * r) + j) < n_pre)) (PreH4 : ((0 : Int) <= INT_MAX)) (PreH5 : ((0 : Int) >= INT_MIN)) (PreH6 : (j ≠ (r - 1))) (PreH7 : (j ≠ (0 : Int))) (PreH8 : (i ≠ (r - 1))) (PreH9 : (i ≠ (0 : Int))) (PreH10 : (j < r)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((Zlength (bits)) = n_pre)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH15 : (Pre bits)) (PreH16 : (1 <= r)) (PreH17 : (r <= 447)) (PreH18 : ((r * r) = n_pre)) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i < r)) (PreH21 : ((0 : Int) <= j)) (PreH22 : (j <= r)) (PreH23 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH24 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  (charArray.full s_pre n_pre bits)
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((Zlength (bits)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49))) ” &&
  “ (Pre bits) ” &&
  “ (1 <= r) ” &&
  “ (r <= 447) ” &&
  “ ((r * r) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < r) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= r) ” &&
  “ forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48)))) ” &&
  “ forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < (j + 1))) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48)))) ”
  &&  (charArray.full s_pre n_pre bits)

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (i : Int) (r : Int) (PreH1 : (i >= r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH6 : (Pre bits)) (PreH7 : (1 <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= r)) (PreH12 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) ,
  (charArray.full s_pre n_pre bits)
|--
  “ (Spec bits 1) ”
  &&  (charArray.full s_pre n_pre bits)
) \/
(
forall (bits : (List Int)) (n_pre : Int) (i : Int) (r : Int) (PreH1 : (i >= r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH6 : (Pre bits)) (PreH7 : (1 <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= r)) (PreH12 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) ,
  TT && emp 
|--
  “ (Spec bits 1) ”
  &&  emp
)

noncomputable def solver_return_wit_1_split_goal_1 : Prop :=
  forall (bits : (List Int)) (n_pre : Int) (i : Int) (r : Int) (PreH1 : (i >= r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH6 : (Pre bits)) (PreH7 : (1 <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r) = n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= r)) (PreH12 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) ,
  (Spec bits 1)

noncomputable def solver_return_wit_2 : Prop :=
  (
forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((Znth ((i * r) + j) bits (0 : Int)) ≠ 49)) (PreH2 : ((0 : Int) <= ((i * r) + j))) (PreH3 : (((i * r) + j) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (j = (0 : Int))) (PreH7 : (i ≠ (r - 1))) (PreH8 : (i ≠ (0 : Int))) (PreH9 : (j < r)) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 200000)) (PreH12 : ((Zlength (bits)) = n_pre)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH14 : (Pre bits)) (PreH15 : (1 <= r)) (PreH16 : (r <= 447)) (PreH17 : ((r * r) = n_pre)) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i < r)) (PreH20 : ((0 : Int) <= j)) (PreH21 : (j <= r)) (PreH22 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH23 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  (charArray.full s_pre n_pre bits)
|--
  “ (Spec bits (0 : Int)) ”
  &&  (charArray.full s_pre n_pre bits)
) \/
(
forall (bits : (List Int)) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((Znth ((i * r) + j) bits (0 : Int)) ≠ 49)) (PreH2 : ((0 : Int) <= ((i * r) + j))) (PreH3 : (((i * r) + j) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (j = (0 : Int))) (PreH7 : (i ≠ (r - 1))) (PreH8 : (i ≠ (0 : Int))) (PreH9 : (j < r)) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 200000)) (PreH12 : ((Zlength (bits)) = n_pre)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH14 : (Pre bits)) (PreH15 : (1 <= r)) (PreH16 : (r <= 447)) (PreH17 : ((r * r) = n_pre)) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i < r)) (PreH20 : ((0 : Int) <= j)) (PreH21 : (j <= r)) (PreH22 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH23 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  TT && emp 
|--
  “ (Spec bits (0 : Int)) ”
  &&  emp
)

noncomputable def solver_return_wit_2_split_goal_1 : Prop :=
  forall (bits : (List Int)) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((Znth ((i * r) + j) bits (0 : Int)) ≠ 49)) (PreH2 : ((0 : Int) <= ((i * r) + j))) (PreH3 : (((i * r) + j) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (j = (0 : Int))) (PreH7 : (i ≠ (r - 1))) (PreH8 : (i ≠ (0 : Int))) (PreH9 : (j < r)) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 200000)) (PreH12 : ((Zlength (bits)) = n_pre)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH14 : (Pre bits)) (PreH15 : (1 <= r)) (PreH16 : (r <= 447)) (PreH17 : ((r * r) = n_pre)) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i < r)) (PreH20 : ((0 : Int) <= j)) (PreH21 : (j <= r)) (PreH22 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH23 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  (Spec bits (0 : Int))

noncomputable def solver_return_wit_3 : Prop :=
  (
forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((Znth ((i * r) + j) bits (0 : Int)) ≠ 49)) (PreH2 : ((0 : Int) <= ((i * r) + j))) (PreH3 : (((i * r) + j) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (i = (0 : Int))) (PreH7 : (j < r)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : ((Zlength (bits)) = n_pre)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH12 : (Pre bits)) (PreH13 : (1 <= r)) (PreH14 : (r <= 447)) (PreH15 : ((r * r) = n_pre)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < r)) (PreH18 : ((0 : Int) <= j)) (PreH19 : (j <= r)) (PreH20 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH21 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  (charArray.full s_pre n_pre bits)
|--
  “ (Spec bits (0 : Int)) ”
  &&  (charArray.full s_pre n_pre bits)
) \/
(
forall (bits : (List Int)) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((Znth ((i * r) + j) bits (0 : Int)) ≠ 49)) (PreH2 : ((0 : Int) <= ((i * r) + j))) (PreH3 : (((i * r) + j) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (i = (0 : Int))) (PreH7 : (j < r)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : ((Zlength (bits)) = n_pre)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH12 : (Pre bits)) (PreH13 : (1 <= r)) (PreH14 : (r <= 447)) (PreH15 : ((r * r) = n_pre)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < r)) (PreH18 : ((0 : Int) <= j)) (PreH19 : (j <= r)) (PreH20 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH21 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  TT && emp 
|--
  “ (Spec bits (0 : Int)) ”
  &&  emp
)

noncomputable def solver_return_wit_3_split_goal_1 : Prop :=
  forall (bits : (List Int)) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((Znth ((i * r) + j) bits (0 : Int)) ≠ 49)) (PreH2 : ((0 : Int) <= ((i * r) + j))) (PreH3 : (((i * r) + j) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (i = (0 : Int))) (PreH7 : (j < r)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : ((Zlength (bits)) = n_pre)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH12 : (Pre bits)) (PreH13 : (1 <= r)) (PreH14 : (r <= 447)) (PreH15 : ((r * r) = n_pre)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < r)) (PreH18 : ((0 : Int) <= j)) (PreH19 : (j <= r)) (PreH20 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH21 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  (Spec bits (0 : Int))

noncomputable def solver_return_wit_4 : Prop :=
  (
forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((Znth ((i * r) + j) bits (0 : Int)) ≠ 49)) (PreH2 : ((0 : Int) <= ((i * r) + j))) (PreH3 : (((i * r) + j) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (i = (r - 1))) (PreH7 : (i ≠ (0 : Int))) (PreH8 : (j < r)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : ((Zlength (bits)) = n_pre)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH13 : (Pre bits)) (PreH14 : (1 <= r)) (PreH15 : (r <= 447)) (PreH16 : ((r * r) = n_pre)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < r)) (PreH19 : ((0 : Int) <= j)) (PreH20 : (j <= r)) (PreH21 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH22 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  (charArray.full s_pre n_pre bits)
|--
  “ (Spec bits (0 : Int)) ”
  &&  (charArray.full s_pre n_pre bits)
) \/
(
forall (bits : (List Int)) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((Znth ((i * r) + j) bits (0 : Int)) ≠ 49)) (PreH2 : ((0 : Int) <= ((i * r) + j))) (PreH3 : (((i * r) + j) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (i = (r - 1))) (PreH7 : (i ≠ (0 : Int))) (PreH8 : (j < r)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : ((Zlength (bits)) = n_pre)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH13 : (Pre bits)) (PreH14 : (1 <= r)) (PreH15 : (r <= 447)) (PreH16 : ((r * r) = n_pre)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < r)) (PreH19 : ((0 : Int) <= j)) (PreH20 : (j <= r)) (PreH21 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH22 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  TT && emp 
|--
  “ (Spec bits (0 : Int)) ”
  &&  emp
)

noncomputable def solver_return_wit_4_split_goal_1 : Prop :=
  forall (bits : (List Int)) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((Znth ((i * r) + j) bits (0 : Int)) ≠ 49)) (PreH2 : ((0 : Int) <= ((i * r) + j))) (PreH3 : (((i * r) + j) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (i = (r - 1))) (PreH7 : (i ≠ (0 : Int))) (PreH8 : (j < r)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : ((Zlength (bits)) = n_pre)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH13 : (Pre bits)) (PreH14 : (1 <= r)) (PreH15 : (r <= 447)) (PreH16 : ((r * r) = n_pre)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < r)) (PreH19 : ((0 : Int) <= j)) (PreH20 : (j <= r)) (PreH21 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH22 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  (Spec bits (0 : Int))

noncomputable def solver_return_wit_5 : Prop :=
  (
forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((Znth ((i * r) + j) bits (0 : Int)) ≠ 49)) (PreH2 : ((0 : Int) <= ((i * r) + j))) (PreH3 : (((i * r) + j) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (j = (r - 1))) (PreH7 : (j ≠ (0 : Int))) (PreH8 : (i ≠ (r - 1))) (PreH9 : (i ≠ (0 : Int))) (PreH10 : (j < r)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((Zlength (bits)) = n_pre)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH15 : (Pre bits)) (PreH16 : (1 <= r)) (PreH17 : (r <= 447)) (PreH18 : ((r * r) = n_pre)) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i < r)) (PreH21 : ((0 : Int) <= j)) (PreH22 : (j <= r)) (PreH23 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH24 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  (charArray.full s_pre n_pre bits)
|--
  “ (Spec bits (0 : Int)) ”
  &&  (charArray.full s_pre n_pre bits)
) \/
(
forall (bits : (List Int)) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((Znth ((i * r) + j) bits (0 : Int)) ≠ 49)) (PreH2 : ((0 : Int) <= ((i * r) + j))) (PreH3 : (((i * r) + j) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (j = (r - 1))) (PreH7 : (j ≠ (0 : Int))) (PreH8 : (i ≠ (r - 1))) (PreH9 : (i ≠ (0 : Int))) (PreH10 : (j < r)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((Zlength (bits)) = n_pre)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH15 : (Pre bits)) (PreH16 : (1 <= r)) (PreH17 : (r <= 447)) (PreH18 : ((r * r) = n_pre)) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i < r)) (PreH21 : ((0 : Int) <= j)) (PreH22 : (j <= r)) (PreH23 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH24 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  TT && emp 
|--
  “ (Spec bits (0 : Int)) ”
  &&  emp
)

noncomputable def solver_return_wit_5_split_goal_1 : Prop :=
  forall (bits : (List Int)) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((Znth ((i * r) + j) bits (0 : Int)) ≠ 49)) (PreH2 : ((0 : Int) <= ((i * r) + j))) (PreH3 : (((i * r) + j) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (j = (r - 1))) (PreH7 : (j ≠ (0 : Int))) (PreH8 : (i ≠ (r - 1))) (PreH9 : (i ≠ (0 : Int))) (PreH10 : (j < r)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((Zlength (bits)) = n_pre)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH15 : (Pre bits)) (PreH16 : (1 <= r)) (PreH17 : (r <= 447)) (PreH18 : ((r * r) = n_pre)) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i < r)) (PreH21 : ((0 : Int) <= j)) (PreH22 : (j <= r)) (PreH23 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH24 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  (Spec bits (0 : Int))

noncomputable def solver_return_wit_6 : Prop :=
  (
forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((Znth ((i * r) + j) bits (0 : Int)) ≠ 48)) (PreH2 : ((0 : Int) <= ((i * r) + j))) (PreH3 : (((i * r) + j) < n_pre)) (PreH4 : ((0 : Int) <= INT_MAX)) (PreH5 : ((0 : Int) >= INT_MIN)) (PreH6 : (j ≠ (r - 1))) (PreH7 : (j ≠ (0 : Int))) (PreH8 : (i ≠ (r - 1))) (PreH9 : (i ≠ (0 : Int))) (PreH10 : (j < r)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((Zlength (bits)) = n_pre)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH15 : (Pre bits)) (PreH16 : (1 <= r)) (PreH17 : (r <= 447)) (PreH18 : ((r * r) = n_pre)) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i < r)) (PreH21 : ((0 : Int) <= j)) (PreH22 : (j <= r)) (PreH23 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH24 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  (charArray.full s_pre n_pre bits)
|--
  “ (Spec bits (0 : Int)) ”
  &&  (charArray.full s_pre n_pre bits)
) \/
(
forall (bits : (List Int)) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((Znth ((i * r) + j) bits (0 : Int)) ≠ 48)) (PreH2 : ((0 : Int) <= ((i * r) + j))) (PreH3 : (((i * r) + j) < n_pre)) (PreH4 : ((0 : Int) <= INT_MAX)) (PreH5 : ((0 : Int) >= INT_MIN)) (PreH6 : (j ≠ (r - 1))) (PreH7 : (j ≠ (0 : Int))) (PreH8 : (i ≠ (r - 1))) (PreH9 : (i ≠ (0 : Int))) (PreH10 : (j < r)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((Zlength (bits)) = n_pre)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH15 : (Pre bits)) (PreH16 : (1 <= r)) (PreH17 : (r <= 447)) (PreH18 : ((r * r) = n_pre)) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i < r)) (PreH21 : ((0 : Int) <= j)) (PreH22 : (j <= r)) (PreH23 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH24 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  TT && emp 
|--
  “ (Spec bits (0 : Int)) ”
  &&  emp
)

noncomputable def solver_return_wit_6_split_goal_1 : Prop :=
  forall (bits : (List Int)) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((Znth ((i * r) + j) bits (0 : Int)) ≠ 48)) (PreH2 : ((0 : Int) <= ((i * r) + j))) (PreH3 : (((i * r) + j) < n_pre)) (PreH4 : ((0 : Int) <= INT_MAX)) (PreH5 : ((0 : Int) >= INT_MIN)) (PreH6 : (j ≠ (r - 1))) (PreH7 : (j ≠ (0 : Int))) (PreH8 : (i ≠ (r - 1))) (PreH9 : (i ≠ (0 : Int))) (PreH10 : (j < r)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((Zlength (bits)) = n_pre)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH15 : (Pre bits)) (PreH16 : (1 <= r)) (PreH17 : (r <= 447)) (PreH18 : ((r * r) = n_pre)) (PreH19 : ((0 : Int) <= i)) (PreH20 : (i < r)) (PreH21 : ((0 : Int) <= j)) (PreH22 : (j <= r)) (PreH23 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH24 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  (Spec bits (0 : Int))

noncomputable def solver_return_wit_7 : Prop :=
  (
forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (r : Int) (PreH1 : ((r * r) ≠ n_pre)) (PreH2 : (((r + 1) * (r + 1)) > n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (bits)) = n_pre)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH7 : (Pre bits)) (PreH8 : ((0 : Int) <= r)) (PreH9 : (r <= 447)) (PreH10 : ((r * r) <= n_pre)) ,
  (charArray.full s_pre n_pre bits)
|--
  “ (Spec bits (0 : Int)) ”
  &&  (charArray.full s_pre n_pre bits)
) \/
(
forall (bits : (List Int)) (n_pre : Int) (r : Int) (PreH1 : ((r * r) ≠ n_pre)) (PreH2 : (((r + 1) * (r + 1)) > n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (bits)) = n_pre)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH7 : (Pre bits)) (PreH8 : ((0 : Int) <= r)) (PreH9 : (r <= 447)) (PreH10 : ((r * r) <= n_pre)) ,
  TT && emp 
|--
  “ (Spec bits (0 : Int)) ”
  &&  emp
)

noncomputable def solver_return_wit_7_split_goal_1 : Prop :=
  forall (bits : (List Int)) (n_pre : Int) (r : Int) (PreH1 : ((r * r) ≠ n_pre)) (PreH2 : (((r + 1) * (r + 1)) > n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (bits)) = n_pre)) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH7 : (Pre bits)) (PreH8 : ((0 : Int) <= r)) (PreH9 : (r <= 447)) (PreH10 : ((r * r) <= n_pre)) ,
  (Spec bits (0 : Int))

noncomputable def solver_partial_solve_wit_1 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((0 : Int) <= ((i * r) + j))) (PreH2 : (((i * r) + j) < n_pre)) (PreH3 : (1 <= INT_MAX)) (PreH4 : (1 >= INT_MIN)) (PreH5 : (j = (0 : Int))) (PreH6 : (i ≠ (r - 1))) (PreH7 : (i ≠ (0 : Int))) (PreH8 : (j < r)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : ((Zlength (bits)) = n_pre)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH13 : (Pre bits)) (PreH14 : (1 <= r)) (PreH15 : (r <= 447)) (PreH16 : ((r * r) = n_pre)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < r)) (PreH19 : ((0 : Int) <= j)) (PreH20 : (j <= r)) (PreH21 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH22 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  (charArray.full s_pre n_pre bits)
|--
  “ ((0 : Int) <= ((i * r) + j)) ” &&
  “ (((i * r) + j) < n_pre) ” &&
  “ (1 <= INT_MAX) ” &&
  “ (1 >= INT_MIN) ” &&
  “ (j = (0 : Int)) ” &&
  “ (i ≠ (r - 1)) ” &&
  “ (i ≠ (0 : Int)) ” &&
  “ (j < r) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((Zlength (bits)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49))) ” &&
  “ (Pre bits) ” &&
  “ (1 <= r) ” &&
  “ (r <= 447) ” &&
  “ ((r * r) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < r) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= r) ” &&
  “ forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48)))) ” &&
  “ forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48)))) ”
  &&  (((s_pre + (((i * r) + j) * sizeof(CHAR)))) # Char |-> ((Znth ((i * r) + j) bits (0 : Int))))
  ** (charArray.missing_i s_pre ((i * r) + j) (0 : Int) n_pre bits)

noncomputable def solver_partial_solve_wit_2 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((0 : Int) <= ((i * r) + j))) (PreH2 : (((i * r) + j) < n_pre)) (PreH3 : (1 <= INT_MAX)) (PreH4 : (1 >= INT_MIN)) (PreH5 : (i = (0 : Int))) (PreH6 : (j < r)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((Zlength (bits)) = n_pre)) (PreH10 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH11 : (Pre bits)) (PreH12 : (1 <= r)) (PreH13 : (r <= 447)) (PreH14 : ((r * r) = n_pre)) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i < r)) (PreH17 : ((0 : Int) <= j)) (PreH18 : (j <= r)) (PreH19 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH20 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  (charArray.full s_pre n_pre bits)
|--
  “ ((0 : Int) <= ((i * r) + j)) ” &&
  “ (((i * r) + j) < n_pre) ” &&
  “ (1 <= INT_MAX) ” &&
  “ (1 >= INT_MIN) ” &&
  “ (i = (0 : Int)) ” &&
  “ (j < r) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((Zlength (bits)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49))) ” &&
  “ (Pre bits) ” &&
  “ (1 <= r) ” &&
  “ (r <= 447) ” &&
  “ ((r * r) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < r) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= r) ” &&
  “ forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48)))) ” &&
  “ forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48)))) ”
  &&  (((s_pre + (((i * r) + j) * sizeof(CHAR)))) # Char |-> ((Znth ((i * r) + j) bits (0 : Int))))
  ** (charArray.missing_i s_pre ((i * r) + j) (0 : Int) n_pre bits)

noncomputable def solver_partial_solve_wit_3 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((0 : Int) <= ((i * r) + j))) (PreH2 : (((i * r) + j) < n_pre)) (PreH3 : (1 <= INT_MAX)) (PreH4 : (1 >= INT_MIN)) (PreH5 : (i = (r - 1))) (PreH6 : (i ≠ (0 : Int))) (PreH7 : (j < r)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : ((Zlength (bits)) = n_pre)) (PreH11 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH12 : (Pre bits)) (PreH13 : (1 <= r)) (PreH14 : (r <= 447)) (PreH15 : ((r * r) = n_pre)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < r)) (PreH18 : ((0 : Int) <= j)) (PreH19 : (j <= r)) (PreH20 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH21 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  (charArray.full s_pre n_pre bits)
|--
  “ ((0 : Int) <= ((i * r) + j)) ” &&
  “ (((i * r) + j) < n_pre) ” &&
  “ (1 <= INT_MAX) ” &&
  “ (1 >= INT_MIN) ” &&
  “ (i = (r - 1)) ” &&
  “ (i ≠ (0 : Int)) ” &&
  “ (j < r) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((Zlength (bits)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49))) ” &&
  “ (Pre bits) ” &&
  “ (1 <= r) ” &&
  “ (r <= 447) ” &&
  “ ((r * r) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < r) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= r) ” &&
  “ forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48)))) ” &&
  “ forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48)))) ”
  &&  (((s_pre + (((i * r) + j) * sizeof(CHAR)))) # Char |-> ((Znth ((i * r) + j) bits (0 : Int))))
  ** (charArray.missing_i s_pre ((i * r) + j) (0 : Int) n_pre bits)

noncomputable def solver_partial_solve_wit_4 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((0 : Int) <= ((i * r) + j))) (PreH2 : (((i * r) + j) < n_pre)) (PreH3 : (1 <= INT_MAX)) (PreH4 : (1 >= INT_MIN)) (PreH5 : (j = (r - 1))) (PreH6 : (j ≠ (0 : Int))) (PreH7 : (i ≠ (r - 1))) (PreH8 : (i ≠ (0 : Int))) (PreH9 : (j < r)) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 200000)) (PreH12 : ((Zlength (bits)) = n_pre)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH14 : (Pre bits)) (PreH15 : (1 <= r)) (PreH16 : (r <= 447)) (PreH17 : ((r * r) = n_pre)) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i < r)) (PreH20 : ((0 : Int) <= j)) (PreH21 : (j <= r)) (PreH22 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH23 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  (charArray.full s_pre n_pre bits)
|--
  “ ((0 : Int) <= ((i * r) + j)) ” &&
  “ (((i * r) + j) < n_pre) ” &&
  “ (1 <= INT_MAX) ” &&
  “ (1 >= INT_MIN) ” &&
  “ (j = (r - 1)) ” &&
  “ (j ≠ (0 : Int)) ” &&
  “ (i ≠ (r - 1)) ” &&
  “ (i ≠ (0 : Int)) ” &&
  “ (j < r) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((Zlength (bits)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49))) ” &&
  “ (Pre bits) ” &&
  “ (1 <= r) ” &&
  “ (r <= 447) ” &&
  “ ((r * r) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < r) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= r) ” &&
  “ forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48)))) ” &&
  “ forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48)))) ”
  &&  (((s_pre + (((i * r) + j) * sizeof(CHAR)))) # Char |-> ((Znth ((i * r) + j) bits (0 : Int))))
  ** (charArray.missing_i s_pre ((i * r) + j) (0 : Int) n_pre bits)

noncomputable def solver_partial_solve_wit_5 : Prop :=
  forall (bits : (List Int)) (s_pre : Int) (n_pre : Int) (j : Int) (i : Int) (r : Int) (PreH1 : ((0 : Int) <= ((i * r) + j))) (PreH2 : (((i * r) + j) < n_pre)) (PreH3 : ((0 : Int) <= INT_MAX)) (PreH4 : ((0 : Int) >= INT_MIN)) (PreH5 : (j ≠ (r - 1))) (PreH6 : (j ≠ (0 : Int))) (PreH7 : (i ≠ (r - 1))) (PreH8 : (i ≠ (0 : Int))) (PreH9 : (j < r)) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 200000)) (PreH12 : ((Zlength (bits)) = n_pre)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49)))) (PreH14 : (Pre bits)) (PreH15 : (1 <= r)) (PreH16 : (r <= 447)) (PreH17 : ((r * r) = n_pre)) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i < r)) (PreH20 : ((0 : Int) <= j)) (PreH21 : (j <= r)) (PreH22 : forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48))))) (PreH23 : forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48))))) ,
  (charArray.full s_pre n_pre bits)
|--
  “ ((0 : Int) <= ((i * r) + j)) ” &&
  “ (((i * r) + j) < n_pre) ” &&
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((0 : Int) >= INT_MIN) ” &&
  “ (j ≠ (r - 1)) ” &&
  “ (j ≠ (0 : Int)) ” &&
  “ (i ≠ (r - 1)) ” &&
  “ (i ≠ (0 : Int)) ” &&
  “ (j < r) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((Zlength (bits)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> (((Znth k bits (0 : Int)) = 48) ∨ ((Znth k bits (0 : Int)) = 49))) ” &&
  “ (Pre bits) ” &&
  “ (1 <= r) ” &&
  “ (r <= 447) ” &&
  “ ((r * r) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < r) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= r) ” &&
  “ forall (x : Int) , forall (y : Int) , ((((((0 : Int) <= x) ∧ (x < i)) ∧ ((0 : Int) <= y)) ∧ (y < r)) -> ((((((x = (0 : Int)) ∨ (x = (r - 1))) ∨ (y = (0 : Int))) ∨ (y = (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 49)) ∨ (((((x ≠ (0 : Int)) ∧ (x ≠ (r - 1))) ∧ (y ≠ (0 : Int))) ∧ (y ≠ (r - 1))) ∧ ((Znth ((x * r) + y) bits (0 : Int)) = 48)))) ” &&
  “ forall (y_2 : Int) , ((((0 : Int) <= y_2) ∧ (y_2 < j)) -> ((((((i = (0 : Int)) ∨ (i = (r - 1))) ∨ (y_2 = (0 : Int))) ∨ (y_2 = (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 49)) ∨ (((((i ≠ (0 : Int)) ∧ (i ≠ (r - 1))) ∧ (y_2 ≠ (0 : Int))) ∧ (y_2 ≠ (r - 1))) ∧ ((Znth ((i * r) + y_2) bits (0 : Int)) = 48)))) ”
  &&  (((s_pre + (((i * r) + j) * sizeof(CHAR)))) # Char |-> ((Znth ((i * r) + j) bits (0 : Int))))
  ** (charArray.missing_i s_pre ((i * r) + j) (0 : Int) n_pre bits)


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
  proof_of_solver_safety_wit_24 : solver_safety_wit_24
  proof_of_solver_safety_wit_25 : solver_safety_wit_25
  proof_of_solver_safety_wit_26 : solver_safety_wit_26
  proof_of_solver_safety_wit_27 : solver_safety_wit_27
  proof_of_solver_safety_wit_28 : solver_safety_wit_28
  proof_of_solver_safety_wit_29 : solver_safety_wit_29
  proof_of_solver_safety_wit_30 : solver_safety_wit_30
  proof_of_solver_safety_wit_31 : solver_safety_wit_31
  proof_of_solver_safety_wit_32 : solver_safety_wit_32
  proof_of_solver_safety_wit_33 : solver_safety_wit_33
  proof_of_solver_safety_wit_34 : solver_safety_wit_34
  proof_of_solver_safety_wit_35 : solver_safety_wit_35
  proof_of_solver_safety_wit_36 : solver_safety_wit_36
  proof_of_solver_safety_wit_37 : solver_safety_wit_37
  proof_of_solver_safety_wit_38 : solver_safety_wit_38
  proof_of_solver_safety_wit_39 : solver_safety_wit_39
  proof_of_solver_safety_wit_40 : solver_safety_wit_40
  proof_of_solver_safety_wit_41 : solver_safety_wit_41
  proof_of_solver_safety_wit_42 : solver_safety_wit_42
  proof_of_solver_safety_wit_43 : solver_safety_wit_43
  proof_of_solver_safety_wit_44 : solver_safety_wit_44
  proof_of_solver_entail_wit_2 : solver_entail_wit_2
  proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2
  proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1
  proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2
  proof_of_solver_entail_wit_7_3 : solver_entail_wit_7_3
  proof_of_solver_entail_wit_7_4 : solver_entail_wit_7_4
  proof_of_solver_entail_wit_7_5 : solver_entail_wit_7_5
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2
  proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3
  proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4
  proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_3 : solver_entail_wit_3
  proof_of_solver_entail_wit_4 : solver_entail_wit_4
  proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1
  proof_of_solver_entail_wit_5_3 : solver_entail_wit_5_3
  proof_of_solver_entail_wit_5_4 : solver_entail_wit_5_4
  proof_of_solver_entail_wit_5_5 : solver_entail_wit_5_5
  proof_of_solver_entail_wit_6 : solver_entail_wit_6
  proof_of_solver_return_wit_1 : solver_return_wit_1
  proof_of_solver_return_wit_2 : solver_return_wit_2
  proof_of_solver_return_wit_3 : solver_return_wit_3
  proof_of_solver_return_wit_4 : solver_return_wit_4
  proof_of_solver_return_wit_5 : solver_return_wit_5
  proof_of_solver_return_wit_6 : solver_return_wit_6
  proof_of_solver_return_wit_7 : solver_return_wit_7

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P004_2008B_square_or_not_goal
