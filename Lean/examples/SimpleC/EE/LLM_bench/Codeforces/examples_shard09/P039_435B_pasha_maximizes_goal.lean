import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P039_435B_pasha_maximizes_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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
  forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (k_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 19)) (PreH3 : ((0 : Int) <= k_pre)) (PreH4 : (k_pre <= 100)) (PreH5 : (n_pre = (Zlength (digits)))) (PreH6 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((48 <= (Znth i digits (0 : Int))) ∧ ((Znth i digits (0 : Int)) <= 57)))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** (charArray.full d_pre (n_pre + 1) (digits ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (k_pre : Int) (i : Int) (cur : (List Int)) (k : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : ((0 : Int) <= k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (cur)) = n_pre)) (PreH9 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH10 : forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57)))) (PreH11 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur (0 : Int))) ∧ ((Znth p_2 cur (0 : Int)) <= 57)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (GreedyProgress digits k_pre cur i k)) (PreH15 : (GreedySelectionReady cur i k)) ,
  ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (charArray.full d_pre (n_pre + 1) (cur ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (k_pre : Int) (i : Int) (cur : (List Int)) (k : Int) (PreH1 : (k > (0 : Int))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 19)) (PreH5 : ((0 : Int) <= k)) (PreH6 : (k <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (n_pre = (Zlength (digits)))) (PreH9 : ((Zlength (cur)) = n_pre)) (PreH10 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH11 : forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57)))) (PreH12 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur (0 : Int))) ∧ ((Znth p_2 cur (0 : Int)) <= 57)))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (GreedyProgress digits k_pre cur i k)) (PreH16 : (GreedySelectionReady cur i k)) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "best" ) )) # Int |-> (i))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (charArray.full d_pre (n_pre + 1) (cur ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (k_pre : Int) (i : Int) (cur : (List Int)) (k : Int) (PreH1 : (k > (0 : Int))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 19)) (PreH5 : ((0 : Int) <= k)) (PreH6 : (k <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (n_pre = (Zlength (digits)))) (PreH9 : ((Zlength (cur)) = n_pre)) (PreH10 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH11 : forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57)))) (PreH12 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur (0 : Int))) ∧ ((Znth p_2 cur (0 : Int)) <= 57)))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (GreedyProgress digits k_pre cur i k)) (PreH16 : (GreedySelectionReady cur i k)) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "best" ) )) # Int |-> (i))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (charArray.full d_pre (n_pre + 1) (cur ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (k_pre : Int) (best : Int) (j : Int) (i : Int) (cur : (List Int)) (k : Int) (PreH1 : (j < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : ((0 : Int) < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (cur)) = n_pre)) (PreH9 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH10 : forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57)))) (PreH11 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur (0 : Int))) ∧ ((Znth p_2 cur (0 : Int)) <= 57)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((i + 1) <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (j <= ((i + k) + 1))) (PreH17 : (i <= best)) (PreH18 : (best < j)) (PreH19 : (FirstMaximumPrefix cur i j best)) (PreH20 : (GreedyProgress digits k_pre cur i k)) (PreH21 : (GreedySelectionReady cur i k)) ,
  ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (charArray.full d_pre (n_pre + 1) (cur ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ ((j - i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j - i)) ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (k_pre : Int) (best : Int) (j : Int) (i : Int) (cur : (List Int)) (k : Int) (PreH1 : ((Znth j (cur ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) > (Znth best (cur ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH2 : ((j - i) <= k)) (PreH3 : (j < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 19)) (PreH6 : ((0 : Int) < k)) (PreH7 : (k <= k_pre)) (PreH8 : (k_pre <= 100)) (PreH9 : (n_pre = (Zlength (digits)))) (PreH10 : ((Zlength (cur)) = n_pre)) (PreH11 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH12 : forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57)))) (PreH13 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur (0 : Int))) ∧ ((Znth p_2 cur (0 : Int)) <= 57)))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((i + 1) <= j)) (PreH17 : (j <= n_pre)) (PreH18 : (j <= ((i + k) + 1))) (PreH19 : (i <= best)) (PreH20 : (best < j)) (PreH21 : (FirstMaximumPrefix cur i j best)) (PreH22 : (GreedyProgress digits k_pre cur i k)) (PreH23 : (GreedySelectionReady cur i k)) ,
  (charArray.full d_pre (n_pre + 1) (cur ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "best" ) )) # Int |-> (j))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def solver_safety_wit_7 : Prop :=
  forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (k_pre : Int) (best : Int) (j : Int) (i : Int) (cur : (List Int)) (k : Int) (PreH1 : ((Znth j (cur ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) <= (Znth best (cur ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH2 : ((j - i) <= k)) (PreH3 : (j < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 19)) (PreH6 : ((0 : Int) < k)) (PreH7 : (k <= k_pre)) (PreH8 : (k_pre <= 100)) (PreH9 : (n_pre = (Zlength (digits)))) (PreH10 : ((Zlength (cur)) = n_pre)) (PreH11 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH12 : forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57)))) (PreH13 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur (0 : Int))) ∧ ((Znth p_2 cur (0 : Int)) <= 57)))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((i + 1) <= j)) (PreH17 : (j <= n_pre)) (PreH18 : (j <= ((i + k) + 1))) (PreH19 : (i <= best)) (PreH20 : (best < j)) (PreH21 : (FirstMaximumPrefix cur i j best)) (PreH22 : (GreedyProgress digits k_pre cur i k)) (PreH23 : (GreedySelectionReady cur i k)) ,
  (charArray.full d_pre (n_pre + 1) (cur ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def solver_safety_wit_8 : Prop :=
  forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (k_pre : Int) (k : Int) (best : Int) (j : Int) (i : Int) (cur : (List Int)) (before : (List Int)) (start_k : Int) (PreH1 : (j > i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : ((0 : Int) < start_k)) (PreH5 : (start_k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (before)) = n_pre)) (PreH9 : ((Zlength (cur)) = n_pre)) (PreH10 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH11 : forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57)))) (PreH12 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before (0 : Int))) ∧ ((Znth p_2 before (0 : Int)) <= 57)))) (PreH13 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur (0 : Int))) ∧ ((Znth p_3 cur (0 : Int)) <= 57)))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= best)) (PreH18 : (best < n_pre)) (PreH19 : ((best - i) <= start_k)) (PreH20 : (k = (start_k - (best - j)))) (PreH21 : ((0 : Int) <= k)) (PreH22 : (k <= start_k)) (PreH23 : (ReachableFirstMaximum before i start_k best)) (PreH24 : (GreedyProgress digits k_pre before i start_k)) (PreH25 : (GreedySelectionReady before i start_k)) (PreH26 : (GreedyExchangeClosure before i start_k best)) (PreH27 : (cur = (move_left (before) (best) (j)))) ,
  (charArray.full d_pre (n_pre + 1) (cur ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "tmp" ) )) # Char |-> ((Znth j (cur ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ ((j - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j - 1)) ”

noncomputable def solver_safety_wit_9 : Prop :=
  forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (k_pre : Int) (k : Int) (best : Int) (j : Int) (i : Int) (cur : (List Int)) (before : (List Int)) (start_k : Int) (PreH1 : (j > i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : ((0 : Int) < start_k)) (PreH5 : (start_k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (before)) = n_pre)) (PreH9 : ((Zlength (cur)) = n_pre)) (PreH10 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH11 : forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57)))) (PreH12 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before (0 : Int))) ∧ ((Znth p_2 before (0 : Int)) <= 57)))) (PreH13 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur (0 : Int))) ∧ ((Znth p_3 cur (0 : Int)) <= 57)))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= best)) (PreH18 : (best < n_pre)) (PreH19 : ((best - i) <= start_k)) (PreH20 : (k = (start_k - (best - j)))) (PreH21 : ((0 : Int) <= k)) (PreH22 : (k <= start_k)) (PreH23 : (ReachableFirstMaximum before i start_k best)) (PreH24 : (GreedyProgress digits k_pre before i start_k)) (PreH25 : (GreedySelectionReady before i start_k)) (PreH26 : (GreedyExchangeClosure before i start_k best)) (PreH27 : (cur = (move_left (before) (best) (j)))) ,
  (charArray.full d_pre (n_pre + 1) (cur ++ ((0 : Int) :: (@List.nil Int))))
  ** ((( &( "tmp" ) )) # Char |-> ((Znth j (cur ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_10 : Prop :=
  forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (k_pre : Int) (k : Int) (best : Int) (j : Int) (i : Int) (cur : (List Int)) (before : (List Int)) (start_k : Int) (PreH1 : (j > i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : ((0 : Int) < start_k)) (PreH5 : (start_k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (before)) = n_pre)) (PreH9 : ((Zlength (cur)) = n_pre)) (PreH10 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH11 : forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57)))) (PreH12 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before (0 : Int))) ∧ ((Znth p_2 before (0 : Int)) <= 57)))) (PreH13 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur (0 : Int))) ∧ ((Znth p_3 cur (0 : Int)) <= 57)))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= best)) (PreH18 : (best < n_pre)) (PreH19 : ((best - i) <= start_k)) (PreH20 : (k = (start_k - (best - j)))) (PreH21 : ((0 : Int) <= k)) (PreH22 : (k <= start_k)) (PreH23 : (ReachableFirstMaximum before i start_k best)) (PreH24 : (GreedyProgress digits k_pre before i start_k)) (PreH25 : (GreedySelectionReady before i start_k)) (PreH26 : (GreedyExchangeClosure before i start_k best)) (PreH27 : (cur = (move_left (before) (best) (j)))) ,
  (charArray.full d_pre (n_pre + 1) (replace_Znth (j) ((Znth (j - 1) (cur ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))) ((cur ++ ((0 : Int) :: (@List.nil Int))))))
  ** ((( &( "tmp" ) )) # Char |-> ((Znth j (cur ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ ((j - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j - 1)) ”

noncomputable def solver_safety_wit_11 : Prop :=
  forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (k_pre : Int) (k : Int) (best : Int) (j : Int) (i : Int) (cur : (List Int)) (before : (List Int)) (start_k : Int) (PreH1 : (j > i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : ((0 : Int) < start_k)) (PreH5 : (start_k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (before)) = n_pre)) (PreH9 : ((Zlength (cur)) = n_pre)) (PreH10 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH11 : forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57)))) (PreH12 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before (0 : Int))) ∧ ((Znth p_2 before (0 : Int)) <= 57)))) (PreH13 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur (0 : Int))) ∧ ((Znth p_3 cur (0 : Int)) <= 57)))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= best)) (PreH18 : (best < n_pre)) (PreH19 : ((best - i) <= start_k)) (PreH20 : (k = (start_k - (best - j)))) (PreH21 : ((0 : Int) <= k)) (PreH22 : (k <= start_k)) (PreH23 : (ReachableFirstMaximum before i start_k best)) (PreH24 : (GreedyProgress digits k_pre before i start_k)) (PreH25 : (GreedySelectionReady before i start_k)) (PreH26 : (GreedyExchangeClosure before i start_k best)) (PreH27 : (cur = (move_left (before) (best) (j)))) ,
  (charArray.full d_pre (n_pre + 1) (replace_Znth (j) ((Znth (j - 1) (cur ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))) ((cur ++ ((0 : Int) :: (@List.nil Int))))))
  ** ((( &( "tmp" ) )) # Char |-> ((Znth j (cur ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_12 : Prop :=
  forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (k_pre : Int) (k : Int) (best : Int) (j : Int) (i : Int) (cur : (List Int)) (before : (List Int)) (start_k : Int) (PreH1 : (j > i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : ((0 : Int) < start_k)) (PreH5 : (start_k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (before)) = n_pre)) (PreH9 : ((Zlength (cur)) = n_pre)) (PreH10 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH11 : forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57)))) (PreH12 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before (0 : Int))) ∧ ((Znth p_2 before (0 : Int)) <= 57)))) (PreH13 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur (0 : Int))) ∧ ((Znth p_3 cur (0 : Int)) <= 57)))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= best)) (PreH18 : (best < n_pre)) (PreH19 : ((best - i) <= start_k)) (PreH20 : (k = (start_k - (best - j)))) (PreH21 : ((0 : Int) <= k)) (PreH22 : (k <= start_k)) (PreH23 : (ReachableFirstMaximum before i start_k best)) (PreH24 : (GreedyProgress digits k_pre before i start_k)) (PreH25 : (GreedySelectionReady before i start_k)) (PreH26 : (GreedyExchangeClosure before i start_k best)) (PreH27 : (cur = (move_left (before) (best) (j)))) ,
  (charArray.full d_pre (n_pre + 1) (replace_Znth ((j - 1)) ((Znth j (cur ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))) ((replace_Znth (j) ((Znth (j - 1) (cur ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))) ((cur ++ ((0 : Int) :: (@List.nil Int))))))))
  ** ((( &( "tmp" ) )) # Char |-> ((Znth j (cur ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ ((k - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k - 1)) ”

noncomputable def solver_safety_wit_13 : Prop :=
  forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (k_pre : Int) (k : Int) (best : Int) (j : Int) (i : Int) (cur : (List Int)) (before : (List Int)) (start_k : Int) (PreH1 : (j > i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : ((0 : Int) < start_k)) (PreH5 : (start_k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (before)) = n_pre)) (PreH9 : ((Zlength (cur)) = n_pre)) (PreH10 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH11 : forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57)))) (PreH12 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before (0 : Int))) ∧ ((Znth p_2 before (0 : Int)) <= 57)))) (PreH13 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur (0 : Int))) ∧ ((Znth p_3 cur (0 : Int)) <= 57)))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= best)) (PreH18 : (best < n_pre)) (PreH19 : ((best - i) <= start_k)) (PreH20 : (k = (start_k - (best - j)))) (PreH21 : ((0 : Int) <= k)) (PreH22 : (k <= start_k)) (PreH23 : (ReachableFirstMaximum before i start_k best)) (PreH24 : (GreedyProgress digits k_pre before i start_k)) (PreH25 : (GreedySelectionReady before i start_k)) (PreH26 : (GreedyExchangeClosure before i start_k best)) (PreH27 : (cur = (move_left (before) (best) (j)))) ,
  (charArray.full d_pre (n_pre + 1) (replace_Znth ((j - 1)) ((Znth j (cur ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))) ((replace_Znth (j) ((Znth (j - 1) (cur ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))) ((cur ++ ((0 : Int) :: (@List.nil Int))))))))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "k" ) )) # Int |-> ((k - 1)))
|--
  “ ((j - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j - 1)) ”

noncomputable def solver_safety_wit_14 : Prop :=
  forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (k_pre : Int) (k : Int) (best : Int) (j : Int) (i : Int) (cur : (List Int)) (before : (List Int)) (start_k : Int) (PreH1 : (j <= i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : ((0 : Int) < start_k)) (PreH5 : (start_k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (before)) = n_pre)) (PreH9 : ((Zlength (cur)) = n_pre)) (PreH10 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH11 : forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57)))) (PreH12 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before (0 : Int))) ∧ ((Znth p_2 before (0 : Int)) <= 57)))) (PreH13 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur (0 : Int))) ∧ ((Znth p_3 cur (0 : Int)) <= 57)))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= best)) (PreH18 : (best < n_pre)) (PreH19 : ((best - i) <= start_k)) (PreH20 : (k = (start_k - (best - j)))) (PreH21 : ((0 : Int) <= k)) (PreH22 : (k <= start_k)) (PreH23 : (ReachableFirstMaximum before i start_k best)) (PreH24 : (GreedyProgress digits k_pre before i start_k)) (PreH25 : (GreedySelectionReady before i start_k)) (PreH26 : (GreedyExchangeClosure before i start_k best)) (PreH27 : (cur = (move_left (before) (best) (j)))) ,
  ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (charArray.full d_pre (n_pre + 1) (cur ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (k_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 19)) (PreH3 : ((0 : Int) <= k_pre)) (PreH4 : (k_pre <= 100)) (PreH5 : (n_pre = (Zlength (digits)))) (PreH6 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((48 <= (Znth i digits (0 : Int))) ∧ ((Znth i digits (0 : Int)) <= 57)))) ,
  (charArray.full d_pre (n_pre + 1) (digits ++ ((0 : Int) :: (@List.nil Int))))
|--
  EX cur : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 19) ” &&
  “ ((0 : Int) <= k_pre) ” &&
  “ (k_pre <= k_pre) ” &&
  “ (k_pre <= 100) ” &&
  “ (n_pre = (Zlength (digits))) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ ((Znth (0 : Int) digits (0 : Int)) ≠ 48) ” &&
  “ forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57))) ” &&
  “ forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur (0 : Int))) ∧ ((Znth p_2 cur (0 : Int)) <= 57))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (GreedyProgress digits k_pre cur (0 : Int) k_pre) ” &&
  “ (GreedySelectionReady cur (0 : Int) k_pre) ”
  &&  (charArray.full d_pre (n_pre + 1) (cur ++ ((0 : Int) :: (@List.nil Int))))
) \/
(
forall (digits : (List Int)) (n_pre : Int) (k_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 19)) (PreH3 : ((0 : Int) <= k_pre)) (PreH4 : (k_pre <= 100)) (PreH5 : (n_pre = (Zlength (digits)))) (PreH6 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((48 <= (Znth i digits (0 : Int))) ∧ ((Znth i digits (0 : Int)) <= 57)))) ,
  TT && emp 
|--
  EX cur : (List Int),
  “ ((digits ++ ((0 : Int) :: (@List.nil Int))) = (cur ++ ((0 : Int) :: (@List.nil Int)))) ” &&
  “ (k_pre <= k_pre) ” &&
  “ ((Zlength (cur)) = (Zlength (digits))) ” &&
  “ forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < (Zlength (digits)))) -> ((48 <= (Znth p_2 cur (0 : Int))) ∧ ((Znth p_2 cur (0 : Int)) <= 57))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (Zlength (digits))) ” &&
  “ (GreedyProgress digits k_pre cur (0 : Int) k_pre) ” &&
  “ (GreedySelectionReady cur (0 : Int) k_pre) ”
  &&  emp
)

noncomputable def solver_entail_wit_2 : Prop :=
  (
forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (k_pre : Int) (i : Int) (cur_2 : (List Int)) (k : Int) (PreH1 : (k > (0 : Int))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 19)) (PreH5 : ((0 : Int) <= k)) (PreH6 : (k <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (n_pre = (Zlength (digits)))) (PreH9 : ((Zlength (cur_2)) = n_pre)) (PreH10 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH11 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < n_pre)) -> ((48 <= (Znth p_3 digits (0 : Int))) ∧ ((Znth p_3 digits (0 : Int)) <= 57)))) (PreH12 : forall (p_4 : Int) , ((((0 : Int) <= p_4) ∧ (p_4 < n_pre)) -> ((48 <= (Znth p_4 cur_2 (0 : Int))) ∧ ((Znth p_4 cur_2 (0 : Int)) <= 57)))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (GreedyProgress digits k_pre cur_2 i k)) (PreH16 : (GreedySelectionReady cur_2 i k)) ,
  (charArray.full d_pre (n_pre + 1) (cur_2 ++ ((0 : Int) :: (@List.nil Int))))
|--
  EX cur : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 19) ” &&
  “ ((0 : Int) < k) ” &&
  “ (k <= k_pre) ” &&
  “ (k_pre <= 100) ” &&
  “ (n_pre = (Zlength (digits))) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ ((Znth (0 : Int) digits (0 : Int)) ≠ 48) ” &&
  “ forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57))) ” &&
  “ forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur (0 : Int))) ∧ ((Znth p_2 cur (0 : Int)) <= 57))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((i + 1) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((i + 1) <= ((i + k) + 1)) ” &&
  “ (i <= i) ” &&
  “ (i < (i + 1)) ” &&
  “ (FirstMaximumPrefix cur i (i + 1) i) ” &&
  “ (GreedyProgress digits k_pre cur i k) ” &&
  “ (GreedySelectionReady cur i k) ”
  &&  (charArray.full d_pre (n_pre + 1) (cur ++ ((0 : Int) :: (@List.nil Int))))
) \/
(
forall (digits : (List Int)) (n_pre : Int) (k_pre : Int) (i : Int) (cur_2 : (List Int)) (k : Int) (PreH1 : (k > (0 : Int))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 19)) (PreH5 : ((0 : Int) <= k)) (PreH6 : (k <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (n_pre = (Zlength (digits)))) (PreH9 : ((Zlength (cur_2)) = n_pre)) (PreH10 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH11 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < n_pre)) -> ((48 <= (Znth p_3 digits (0 : Int))) ∧ ((Znth p_3 digits (0 : Int)) <= 57)))) (PreH12 : forall (p_4 : Int) , ((((0 : Int) <= p_4) ∧ (p_4 < n_pre)) -> ((48 <= (Znth p_4 cur_2 (0 : Int))) ∧ ((Znth p_4 cur_2 (0 : Int)) <= 57)))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (GreedyProgress digits k_pre cur_2 i k)) (PreH16 : (GreedySelectionReady cur_2 i k)) ,
  TT && emp 
|--
  EX cur : (List Int),
  “ ((cur_2 ++ ((0 : Int) :: (@List.nil Int))) = (cur ++ ((0 : Int) :: (@List.nil Int)))) ” &&
  “ ((0 : Int) < k) ” &&
  “ ((Zlength (cur)) = (Zlength (digits))) ” &&
  “ forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < (Zlength (digits)))) -> ((48 <= (Znth p_2 cur (0 : Int))) ∧ ((Znth p_2 cur (0 : Int)) <= 57))) ” &&
  “ ((i + 1) <= (i + 1)) ” &&
  “ ((i + 1) <= (Zlength (digits))) ” &&
  “ ((i + 1) <= ((i + k) + 1)) ” &&
  “ (i <= i) ” &&
  “ (i < (i + 1)) ” &&
  “ (FirstMaximumPrefix cur i (i + 1) i) ” &&
  “ (GreedyProgress digits k_pre cur i k) ” &&
  “ (GreedySelectionReady cur i k) ”
  &&  emp
)

noncomputable def solver_entail_wit_3_1 : Prop :=
  (
forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (k_pre : Int) (best : Int) (j : Int) (i : Int) (cur_2 : (List Int)) (k : Int) (PreH1 : ((Znth j (cur_2 ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) > (Znth best (cur_2 ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH2 : ((j - i) <= k)) (PreH3 : (j < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 19)) (PreH6 : ((0 : Int) < k)) (PreH7 : (k <= k_pre)) (PreH8 : (k_pre <= 100)) (PreH9 : (n_pre = (Zlength (digits)))) (PreH10 : ((Zlength (cur_2)) = n_pre)) (PreH11 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH12 : forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57)))) (PreH13 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur_2 (0 : Int))) ∧ ((Znth p_2 cur_2 (0 : Int)) <= 57)))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((i + 1) <= j)) (PreH17 : (j <= n_pre)) (PreH18 : (j <= ((i + k) + 1))) (PreH19 : (i <= best)) (PreH20 : (best < j)) (PreH21 : (FirstMaximumPrefix cur_2 i j best)) (PreH22 : (GreedyProgress digits k_pre cur_2 i k)) (PreH23 : (GreedySelectionReady cur_2 i k)) ,
  (charArray.full d_pre (n_pre + 1) (cur_2 ++ ((0 : Int) :: (@List.nil Int))))
|--
  EX cur : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 19) ” &&
  “ ((0 : Int) < k) ” &&
  “ (k <= k_pre) ” &&
  “ (k_pre <= 100) ” &&
  “ (n_pre = (Zlength (digits))) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ ((Znth (0 : Int) digits (0 : Int)) ≠ 48) ” &&
  “ forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57))) ” &&
  “ forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur (0 : Int))) ∧ ((Znth p_2 cur (0 : Int)) <= 57))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((i + 1) <= (j + 1)) ” &&
  “ ((j + 1) <= n_pre) ” &&
  “ ((j + 1) <= ((i + k) + 1)) ” &&
  “ (i <= j) ” &&
  “ (j < (j + 1)) ” &&
  “ (FirstMaximumPrefix cur i (j + 1) j) ” &&
  “ (GreedyProgress digits k_pre cur i k) ” &&
  “ (GreedySelectionReady cur i k) ”
  &&  (charArray.full d_pre (n_pre + 1) (cur ++ ((0 : Int) :: (@List.nil Int))))
) \/
(
forall (digits : (List Int)) (n_pre : Int) (k_pre : Int) (best : Int) (j : Int) (i : Int) (cur_2 : (List Int)) (k : Int) (PreH1 : ((Znth j (cur_2 ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) > (Znth best (cur_2 ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH2 : ((j - i) <= k)) (PreH3 : (j < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 19)) (PreH6 : ((0 : Int) < k)) (PreH7 : (k <= k_pre)) (PreH8 : (k_pre <= 100)) (PreH9 : (n_pre = (Zlength (digits)))) (PreH10 : ((Zlength (cur_2)) = n_pre)) (PreH11 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH12 : forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57)))) (PreH13 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur_2 (0 : Int))) ∧ ((Znth p_2 cur_2 (0 : Int)) <= 57)))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((i + 1) <= j)) (PreH17 : (j <= n_pre)) (PreH18 : (j <= ((i + k) + 1))) (PreH19 : (i <= best)) (PreH20 : (best < j)) (PreH21 : (FirstMaximumPrefix cur_2 i j best)) (PreH22 : (GreedyProgress digits k_pre cur_2 i k)) (PreH23 : (GreedySelectionReady cur_2 i k)) ,
  TT && emp 
|--
  EX cur : (List Int),
  “ ((cur_2 ++ ((0 : Int) :: (@List.nil Int))) = (cur ++ ((0 : Int) :: (@List.nil Int)))) ” &&
  “ ((Zlength (cur)) = (Zlength (digits))) ” &&
  “ forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < (Zlength (digits)))) -> ((48 <= (Znth p_2 cur (0 : Int))) ∧ ((Znth p_2 cur (0 : Int)) <= 57))) ” &&
  “ ((i + 1) <= (j + 1)) ” &&
  “ ((j + 1) <= (Zlength (digits))) ” &&
  “ ((j + 1) <= ((i + k) + 1)) ” &&
  “ (i <= j) ” &&
  “ (j < (j + 1)) ” &&
  “ (FirstMaximumPrefix cur i (j + 1) j) ” &&
  “ (GreedyProgress digits k_pre cur i k) ” &&
  “ (GreedySelectionReady cur i k) ”
  &&  emp
)

noncomputable def solver_entail_wit_3_2 : Prop :=
  (
forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (k_pre : Int) (best : Int) (j : Int) (i : Int) (cur_2 : (List Int)) (k : Int) (PreH1 : ((Znth j (cur_2 ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) <= (Znth best (cur_2 ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH2 : ((j - i) <= k)) (PreH3 : (j < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 19)) (PreH6 : ((0 : Int) < k)) (PreH7 : (k <= k_pre)) (PreH8 : (k_pre <= 100)) (PreH9 : (n_pre = (Zlength (digits)))) (PreH10 : ((Zlength (cur_2)) = n_pre)) (PreH11 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH12 : forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57)))) (PreH13 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur_2 (0 : Int))) ∧ ((Znth p_2 cur_2 (0 : Int)) <= 57)))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((i + 1) <= j)) (PreH17 : (j <= n_pre)) (PreH18 : (j <= ((i + k) + 1))) (PreH19 : (i <= best)) (PreH20 : (best < j)) (PreH21 : (FirstMaximumPrefix cur_2 i j best)) (PreH22 : (GreedyProgress digits k_pre cur_2 i k)) (PreH23 : (GreedySelectionReady cur_2 i k)) ,
  (charArray.full d_pre (n_pre + 1) (cur_2 ++ ((0 : Int) :: (@List.nil Int))))
|--
  EX cur : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 19) ” &&
  “ ((0 : Int) < k) ” &&
  “ (k <= k_pre) ” &&
  “ (k_pre <= 100) ” &&
  “ (n_pre = (Zlength (digits))) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ ((Znth (0 : Int) digits (0 : Int)) ≠ 48) ” &&
  “ forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57))) ” &&
  “ forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur (0 : Int))) ∧ ((Znth p_2 cur (0 : Int)) <= 57))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((i + 1) <= (j + 1)) ” &&
  “ ((j + 1) <= n_pre) ” &&
  “ ((j + 1) <= ((i + k) + 1)) ” &&
  “ (i <= best) ” &&
  “ (best < (j + 1)) ” &&
  “ (FirstMaximumPrefix cur i (j + 1) best) ” &&
  “ (GreedyProgress digits k_pre cur i k) ” &&
  “ (GreedySelectionReady cur i k) ”
  &&  (charArray.full d_pre (n_pre + 1) (cur ++ ((0 : Int) :: (@List.nil Int))))
) \/
(
forall (digits : (List Int)) (n_pre : Int) (k_pre : Int) (best : Int) (j : Int) (i : Int) (cur_2 : (List Int)) (k : Int) (PreH1 : ((Znth j (cur_2 ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)) <= (Znth best (cur_2 ++ ((0 : Int) :: (@List.nil Int))) (0 : Int)))) (PreH2 : ((j - i) <= k)) (PreH3 : (j < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 19)) (PreH6 : ((0 : Int) < k)) (PreH7 : (k <= k_pre)) (PreH8 : (k_pre <= 100)) (PreH9 : (n_pre = (Zlength (digits)))) (PreH10 : ((Zlength (cur_2)) = n_pre)) (PreH11 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH12 : forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57)))) (PreH13 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur_2 (0 : Int))) ∧ ((Znth p_2 cur_2 (0 : Int)) <= 57)))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((i + 1) <= j)) (PreH17 : (j <= n_pre)) (PreH18 : (j <= ((i + k) + 1))) (PreH19 : (i <= best)) (PreH20 : (best < j)) (PreH21 : (FirstMaximumPrefix cur_2 i j best)) (PreH22 : (GreedyProgress digits k_pre cur_2 i k)) (PreH23 : (GreedySelectionReady cur_2 i k)) ,
  TT && emp 
|--
  EX cur : (List Int),
  “ ((cur_2 ++ ((0 : Int) :: (@List.nil Int))) = (cur ++ ((0 : Int) :: (@List.nil Int)))) ” &&
  “ ((Zlength (cur)) = (Zlength (digits))) ” &&
  “ forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < (Zlength (digits)))) -> ((48 <= (Znth p_2 cur (0 : Int))) ∧ ((Znth p_2 cur (0 : Int)) <= 57))) ” &&
  “ ((i + 1) <= (j + 1)) ” &&
  “ ((j + 1) <= (Zlength (digits))) ” &&
  “ ((j + 1) <= ((i + k) + 1)) ” &&
  “ (best < (j + 1)) ” &&
  “ (FirstMaximumPrefix cur i (j + 1) best) ” &&
  “ (GreedyProgress digits k_pre cur i k) ” &&
  “ (GreedySelectionReady cur i k) ”
  &&  emp
)

noncomputable def solver_entail_wit_4_1 : Prop :=
  (
forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (k_pre : Int) (best : Int) (j : Int) (i : Int) (cur_2 : (List Int)) (k : Int) (PreH1 : (j >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : ((0 : Int) < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (cur_2)) = n_pre)) (PreH9 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH10 : forall (p_4 : Int) , ((((0 : Int) <= p_4) ∧ (p_4 < n_pre)) -> ((48 <= (Znth p_4 digits (0 : Int))) ∧ ((Znth p_4 digits (0 : Int)) <= 57)))) (PreH11 : forall (p_5 : Int) , ((((0 : Int) <= p_5) ∧ (p_5 < n_pre)) -> ((48 <= (Znth p_5 cur_2 (0 : Int))) ∧ ((Znth p_5 cur_2 (0 : Int)) <= 57)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((i + 1) <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (j <= ((i + k) + 1))) (PreH17 : (i <= best)) (PreH18 : (best < j)) (PreH19 : (FirstMaximumPrefix cur_2 i j best)) (PreH20 : (GreedyProgress digits k_pre cur_2 i k)) (PreH21 : (GreedySelectionReady cur_2 i k)) ,
  (charArray.full d_pre (n_pre + 1) (cur_2 ++ ((0 : Int) :: (@List.nil Int))))
|--
  EX cur : (List Int), EX before : (List Int), EX start_k : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 19) ” &&
  “ ((0 : Int) < start_k) ” &&
  “ (start_k <= k_pre) ” &&
  “ (k_pre <= 100) ” &&
  “ (n_pre = (Zlength (digits))) ” &&
  “ ((Zlength (before)) = n_pre) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ ((Znth (0 : Int) digits (0 : Int)) ≠ 48) ” &&
  “ forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57))) ” &&
  “ forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before (0 : Int))) ∧ ((Znth p_2 before (0 : Int)) <= 57))) ” &&
  “ forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur (0 : Int))) ∧ ((Znth p_3 cur (0 : Int)) <= 57))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (i <= best) ” &&
  “ (best <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((best - i) <= start_k) ” &&
  “ (k = (start_k - (best - best))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= start_k) ” &&
  “ (ReachableFirstMaximum before i start_k best) ” &&
  “ (GreedyProgress digits k_pre before i start_k) ” &&
  “ (GreedySelectionReady before i start_k) ” &&
  “ (GreedyExchangeClosure before i start_k best) ” &&
  “ (cur = (move_left (before) (best) (best))) ”
  &&  (charArray.full d_pre (n_pre + 1) (cur ++ ((0 : Int) :: (@List.nil Int))))
) \/
(
forall (digits : (List Int)) (n_pre : Int) (k_pre : Int) (best : Int) (j : Int) (i : Int) (cur_2 : (List Int)) (k : Int) (PreH1 : (j >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : ((0 : Int) < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (cur_2)) = n_pre)) (PreH9 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH10 : forall (p_4 : Int) , ((((0 : Int) <= p_4) ∧ (p_4 < n_pre)) -> ((48 <= (Znth p_4 digits (0 : Int))) ∧ ((Znth p_4 digits (0 : Int)) <= 57)))) (PreH11 : forall (p_5 : Int) , ((((0 : Int) <= p_5) ∧ (p_5 < n_pre)) -> ((48 <= (Znth p_5 cur_2 (0 : Int))) ∧ ((Znth p_5 cur_2 (0 : Int)) <= 57)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((i + 1) <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (j <= ((i + k) + 1))) (PreH17 : (i <= best)) (PreH18 : (best < j)) (PreH19 : (FirstMaximumPrefix cur_2 i j best)) (PreH20 : (GreedyProgress digits k_pre cur_2 i k)) (PreH21 : (GreedySelectionReady cur_2 i k)) ,
  TT && emp 
|--
  EX before : (List Int), EX start_k : Int,
  “ ((cur_2 ++ ((0 : Int) :: (@List.nil Int))) = ((move_left (before) (best) (best)) ++ ((0 : Int) :: (@List.nil Int)))) ” &&
  “ ((0 : Int) < start_k) ” &&
  “ (start_k <= k_pre) ” &&
  “ ((Zlength (before)) = (Zlength (digits))) ” &&
  “ ((Zlength ((move_left (before) (best) (best)))) = (Zlength (digits))) ” &&
  “ forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < (Zlength (digits)))) -> ((48 <= (Znth p_2 before (0 : Int))) ∧ ((Znth p_2 before (0 : Int)) <= 57))) ” &&
  “ forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < (Zlength (digits)))) -> ((48 <= (Znth p_3 (move_left (before) (best) (best)) (0 : Int))) ∧ ((Znth p_3 (move_left (before) (best) (best)) (0 : Int)) <= 57))) ” &&
  “ (best <= best) ” &&
  “ (best < (Zlength (digits))) ” &&
  “ ((best - i) <= start_k) ” &&
  “ (k = (start_k - (best - best))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= start_k) ” &&
  “ (ReachableFirstMaximum before i start_k best) ” &&
  “ (GreedyProgress digits k_pre before i start_k) ” &&
  “ (GreedySelectionReady before i start_k) ” &&
  “ (GreedyExchangeClosure before i start_k best) ”
  &&  emp
)

noncomputable def solver_entail_wit_4_2 : Prop :=
  (
forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (k_pre : Int) (best : Int) (j : Int) (i : Int) (cur_2 : (List Int)) (k : Int) (PreH1 : ((j - i) > k)) (PreH2 : (j < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 19)) (PreH5 : ((0 : Int) < k)) (PreH6 : (k <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (n_pre = (Zlength (digits)))) (PreH9 : ((Zlength (cur_2)) = n_pre)) (PreH10 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH11 : forall (p_4 : Int) , ((((0 : Int) <= p_4) ∧ (p_4 < n_pre)) -> ((48 <= (Znth p_4 digits (0 : Int))) ∧ ((Znth p_4 digits (0 : Int)) <= 57)))) (PreH12 : forall (p_5 : Int) , ((((0 : Int) <= p_5) ∧ (p_5 < n_pre)) -> ((48 <= (Znth p_5 cur_2 (0 : Int))) ∧ ((Znth p_5 cur_2 (0 : Int)) <= 57)))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((i + 1) <= j)) (PreH16 : (j <= n_pre)) (PreH17 : (j <= ((i + k) + 1))) (PreH18 : (i <= best)) (PreH19 : (best < j)) (PreH20 : (FirstMaximumPrefix cur_2 i j best)) (PreH21 : (GreedyProgress digits k_pre cur_2 i k)) (PreH22 : (GreedySelectionReady cur_2 i k)) ,
  (charArray.full d_pre (n_pre + 1) (cur_2 ++ ((0 : Int) :: (@List.nil Int))))
|--
  EX cur : (List Int), EX before : (List Int), EX start_k : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 19) ” &&
  “ ((0 : Int) < start_k) ” &&
  “ (start_k <= k_pre) ” &&
  “ (k_pre <= 100) ” &&
  “ (n_pre = (Zlength (digits))) ” &&
  “ ((Zlength (before)) = n_pre) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ ((Znth (0 : Int) digits (0 : Int)) ≠ 48) ” &&
  “ forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57))) ” &&
  “ forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before (0 : Int))) ∧ ((Znth p_2 before (0 : Int)) <= 57))) ” &&
  “ forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur (0 : Int))) ∧ ((Znth p_3 cur (0 : Int)) <= 57))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (i <= best) ” &&
  “ (best <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((best - i) <= start_k) ” &&
  “ (k = (start_k - (best - best))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= start_k) ” &&
  “ (ReachableFirstMaximum before i start_k best) ” &&
  “ (GreedyProgress digits k_pre before i start_k) ” &&
  “ (GreedySelectionReady before i start_k) ” &&
  “ (GreedyExchangeClosure before i start_k best) ” &&
  “ (cur = (move_left (before) (best) (best))) ”
  &&  (charArray.full d_pre (n_pre + 1) (cur ++ ((0 : Int) :: (@List.nil Int))))
) \/
(
forall (digits : (List Int)) (n_pre : Int) (k_pre : Int) (best : Int) (j : Int) (i : Int) (cur_2 : (List Int)) (k : Int) (PreH1 : ((j - i) > k)) (PreH2 : (j < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 19)) (PreH5 : ((0 : Int) < k)) (PreH6 : (k <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (n_pre = (Zlength (digits)))) (PreH9 : ((Zlength (cur_2)) = n_pre)) (PreH10 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH11 : forall (p_4 : Int) , ((((0 : Int) <= p_4) ∧ (p_4 < n_pre)) -> ((48 <= (Znth p_4 digits (0 : Int))) ∧ ((Znth p_4 digits (0 : Int)) <= 57)))) (PreH12 : forall (p_5 : Int) , ((((0 : Int) <= p_5) ∧ (p_5 < n_pre)) -> ((48 <= (Znth p_5 cur_2 (0 : Int))) ∧ ((Znth p_5 cur_2 (0 : Int)) <= 57)))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((i + 1) <= j)) (PreH16 : (j <= n_pre)) (PreH17 : (j <= ((i + k) + 1))) (PreH18 : (i <= best)) (PreH19 : (best < j)) (PreH20 : (FirstMaximumPrefix cur_2 i j best)) (PreH21 : (GreedyProgress digits k_pre cur_2 i k)) (PreH22 : (GreedySelectionReady cur_2 i k)) ,
  TT && emp 
|--
  EX before : (List Int), EX start_k : Int,
  “ ((cur_2 ++ ((0 : Int) :: (@List.nil Int))) = ((move_left (before) (best) (best)) ++ ((0 : Int) :: (@List.nil Int)))) ” &&
  “ ((0 : Int) < start_k) ” &&
  “ (start_k <= k_pre) ” &&
  “ ((Zlength (before)) = (Zlength (digits))) ” &&
  “ ((Zlength ((move_left (before) (best) (best)))) = (Zlength (digits))) ” &&
  “ forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < (Zlength (digits)))) -> ((48 <= (Znth p_2 before (0 : Int))) ∧ ((Znth p_2 before (0 : Int)) <= 57))) ” &&
  “ forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < (Zlength (digits)))) -> ((48 <= (Znth p_3 (move_left (before) (best) (best)) (0 : Int))) ∧ ((Znth p_3 (move_left (before) (best) (best)) (0 : Int)) <= 57))) ” &&
  “ (best <= best) ” &&
  “ (best < (Zlength (digits))) ” &&
  “ ((best - i) <= start_k) ” &&
  “ (k = (start_k - (best - best))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= start_k) ” &&
  “ (ReachableFirstMaximum before i start_k best) ” &&
  “ (GreedyProgress digits k_pre before i start_k) ” &&
  “ (GreedySelectionReady before i start_k) ” &&
  “ (GreedyExchangeClosure before i start_k best) ”
  &&  emp
)

noncomputable def solver_entail_wit_5 : Prop :=
  (
forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (k_pre : Int) (k : Int) (best : Int) (j : Int) (i : Int) (cur_2 : (List Int)) (before_2 : (List Int)) (start_k_2 : Int) (PreH1 : (j > i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : ((0 : Int) < start_k_2)) (PreH5 : (start_k_2 <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (before_2)) = n_pre)) (PreH9 : ((Zlength (cur_2)) = n_pre)) (PreH10 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH11 : forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57)))) (PreH12 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before_2 (0 : Int))) ∧ ((Znth p_2 before_2 (0 : Int)) <= 57)))) (PreH13 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur_2 (0 : Int))) ∧ ((Znth p_3 cur_2 (0 : Int)) <= 57)))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= best)) (PreH18 : (best < n_pre)) (PreH19 : ((best - i) <= start_k_2)) (PreH20 : (k = (start_k_2 - (best - j)))) (PreH21 : ((0 : Int) <= k)) (PreH22 : (k <= start_k_2)) (PreH23 : (ReachableFirstMaximum before_2 i start_k_2 best)) (PreH24 : (GreedyProgress digits k_pre before_2 i start_k_2)) (PreH25 : (GreedySelectionReady before_2 i start_k_2)) (PreH26 : (GreedyExchangeClosure before_2 i start_k_2 best)) (PreH27 : (cur_2 = (move_left (before_2) (best) (j)))) ,
  (charArray.full d_pre (n_pre + 1) (replace_Znth ((j - 1)) ((Znth j (cur_2 ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))) ((replace_Znth (j) ((Znth (j - 1) (cur_2 ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))) ((cur_2 ++ ((0 : Int) :: (@List.nil Int))))))))
|--
  EX cur : (List Int), EX before : (List Int), EX start_k : Int,
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 19) ” &&
  “ ((0 : Int) < start_k) ” &&
  “ (start_k <= k_pre) ” &&
  “ (k_pre <= 100) ” &&
  “ (n_pre = (Zlength (digits))) ” &&
  “ ((Zlength (before)) = n_pre) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ ((Znth (0 : Int) digits (0 : Int)) ≠ 48) ” &&
  “ forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57))) ” &&
  “ forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before (0 : Int))) ∧ ((Znth p_2 before (0 : Int)) <= 57))) ” &&
  “ forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur (0 : Int))) ∧ ((Znth p_3 cur (0 : Int)) <= 57))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (i <= (j - 1)) ” &&
  “ ((j - 1) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((best - i) <= start_k) ” &&
  “ ((k - 1) = (start_k - (best - (j - 1)))) ” &&
  “ ((0 : Int) <= (k - 1)) ” &&
  “ ((k - 1) <= start_k) ” &&
  “ (ReachableFirstMaximum before i start_k best) ” &&
  “ (GreedyProgress digits k_pre before i start_k) ” &&
  “ (GreedySelectionReady before i start_k) ” &&
  “ (GreedyExchangeClosure before i start_k best) ” &&
  “ (cur = (move_left (before) (best) ((j - 1)))) ”
  &&  (charArray.full d_pre (n_pre + 1) (cur ++ ((0 : Int) :: (@List.nil Int))))
) \/
(
forall (digits : (List Int)) (n_pre : Int) (k_pre : Int) (k : Int) (best : Int) (j : Int) (i : Int) (cur_2 : (List Int)) (before_2 : (List Int)) (start_k_2 : Int) (PreH1 : (j > i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : ((0 : Int) < start_k_2)) (PreH5 : (start_k_2 <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (before_2)) = n_pre)) (PreH9 : ((Zlength (cur_2)) = n_pre)) (PreH10 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH11 : forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57)))) (PreH12 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before_2 (0 : Int))) ∧ ((Znth p_2 before_2 (0 : Int)) <= 57)))) (PreH13 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur_2 (0 : Int))) ∧ ((Znth p_3 cur_2 (0 : Int)) <= 57)))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= best)) (PreH18 : (best < n_pre)) (PreH19 : ((best - i) <= start_k_2)) (PreH20 : (k = (start_k_2 - (best - j)))) (PreH21 : ((0 : Int) <= k)) (PreH22 : (k <= start_k_2)) (PreH23 : (ReachableFirstMaximum before_2 i start_k_2 best)) (PreH24 : (GreedyProgress digits k_pre before_2 i start_k_2)) (PreH25 : (GreedySelectionReady before_2 i start_k_2)) (PreH26 : (GreedyExchangeClosure before_2 i start_k_2 best)) (PreH27 : (cur_2 = (move_left (before_2) (best) (j)))) ,
  TT && emp 
|--
  EX before : (List Int), EX start_k : Int,
  “ ((replace_Znth ((j - 1)) ((Znth j ((move_left (before_2) (best) (j)) ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))) ((replace_Znth (j) ((Znth (j - 1) ((move_left (before_2) (best) (j)) ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))) (((move_left (before_2) (best) (j)) ++ ((0 : Int) :: (@List.nil Int))))))) = ((move_left (before) (best) ((j - 1))) ++ ((0 : Int) :: (@List.nil Int)))) ” &&
  “ ((0 : Int) < start_k) ” &&
  “ (start_k <= k_pre) ” &&
  “ ((Zlength (before)) = (Zlength (digits))) ” &&
  “ ((Zlength ((move_left (before) (best) ((j - 1))))) = (Zlength (digits))) ” &&
  “ forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < (Zlength (digits)))) -> ((48 <= (Znth p_2 before (0 : Int))) ∧ ((Znth p_2 before (0 : Int)) <= 57))) ” &&
  “ forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < (Zlength (digits)))) -> ((48 <= (Znth p_3 (move_left (before) (best) ((j - 1))) (0 : Int))) ∧ ((Znth p_3 (move_left (before) (best) ((j - 1))) (0 : Int)) <= 57))) ” &&
  “ (i <= (j - 1)) ” &&
  “ ((j - 1) <= best) ” &&
  “ ((best - i) <= start_k) ” &&
  “ (((start_k_2 - (best - j)) - 1) = (start_k - (best - (j - 1)))) ” &&
  “ ((0 : Int) <= ((start_k_2 - (best - j)) - 1)) ” &&
  “ (((start_k_2 - (best - j)) - 1) <= start_k) ” &&
  “ (ReachableFirstMaximum before i start_k best) ” &&
  “ (GreedyProgress digits k_pre before i start_k) ” &&
  “ (GreedySelectionReady before i start_k) ” &&
  “ (GreedyExchangeClosure before i start_k best) ”
  &&  emp
)

noncomputable def solver_entail_wit_6 : Prop :=
  (
forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (k_pre : Int) (k : Int) (best : Int) (j : Int) (i : Int) (cur_2 : (List Int)) (before : (List Int)) (start_k : Int) (PreH1 : (j <= i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : ((0 : Int) < start_k)) (PreH5 : (start_k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (before)) = n_pre)) (PreH9 : ((Zlength (cur_2)) = n_pre)) (PreH10 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH11 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < n_pre)) -> ((48 <= (Znth p_3 digits (0 : Int))) ∧ ((Znth p_3 digits (0 : Int)) <= 57)))) (PreH12 : forall (p_4 : Int) , ((((0 : Int) <= p_4) ∧ (p_4 < n_pre)) -> ((48 <= (Znth p_4 before (0 : Int))) ∧ ((Znth p_4 before (0 : Int)) <= 57)))) (PreH13 : forall (p_5 : Int) , ((((0 : Int) <= p_5) ∧ (p_5 < n_pre)) -> ((48 <= (Znth p_5 cur_2 (0 : Int))) ∧ ((Znth p_5 cur_2 (0 : Int)) <= 57)))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= best)) (PreH18 : (best < n_pre)) (PreH19 : ((best - i) <= start_k)) (PreH20 : (k = (start_k - (best - j)))) (PreH21 : ((0 : Int) <= k)) (PreH22 : (k <= start_k)) (PreH23 : (ReachableFirstMaximum before i start_k best)) (PreH24 : (GreedyProgress digits k_pre before i start_k)) (PreH25 : (GreedySelectionReady before i start_k)) (PreH26 : (GreedyExchangeClosure before i start_k best)) (PreH27 : (cur_2 = (move_left (before) (best) (j)))) ,
  (charArray.full d_pre (n_pre + 1) (cur_2 ++ ((0 : Int) :: (@List.nil Int))))
|--
  EX cur : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 19) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= k_pre) ” &&
  “ (k_pre <= 100) ” &&
  “ (n_pre = (Zlength (digits))) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ ((Znth (0 : Int) digits (0 : Int)) ≠ 48) ” &&
  “ forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57))) ” &&
  “ forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur (0 : Int))) ∧ ((Znth p_2 cur (0 : Int)) <= 57))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ (GreedyProgress digits k_pre cur (i + 1) k) ” &&
  “ (GreedySelectionReady cur (i + 1) k) ”
  &&  (charArray.full d_pre (n_pre + 1) (cur ++ ((0 : Int) :: (@List.nil Int))))
) \/
(
forall (digits : (List Int)) (n_pre : Int) (k_pre : Int) (k : Int) (best : Int) (j : Int) (i : Int) (cur_2 : (List Int)) (before : (List Int)) (start_k : Int) (PreH1 : (j <= i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : ((0 : Int) < start_k)) (PreH5 : (start_k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (before)) = n_pre)) (PreH9 : ((Zlength (cur_2)) = n_pre)) (PreH10 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH11 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < n_pre)) -> ((48 <= (Znth p_3 digits (0 : Int))) ∧ ((Znth p_3 digits (0 : Int)) <= 57)))) (PreH12 : forall (p_4 : Int) , ((((0 : Int) <= p_4) ∧ (p_4 < n_pre)) -> ((48 <= (Znth p_4 before (0 : Int))) ∧ ((Znth p_4 before (0 : Int)) <= 57)))) (PreH13 : forall (p_5 : Int) , ((((0 : Int) <= p_5) ∧ (p_5 < n_pre)) -> ((48 <= (Znth p_5 cur_2 (0 : Int))) ∧ ((Znth p_5 cur_2 (0 : Int)) <= 57)))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= best)) (PreH18 : (best < n_pre)) (PreH19 : ((best - i) <= start_k)) (PreH20 : (k = (start_k - (best - j)))) (PreH21 : ((0 : Int) <= k)) (PreH22 : (k <= start_k)) (PreH23 : (ReachableFirstMaximum before i start_k best)) (PreH24 : (GreedyProgress digits k_pre before i start_k)) (PreH25 : (GreedySelectionReady before i start_k)) (PreH26 : (GreedyExchangeClosure before i start_k best)) (PreH27 : (cur_2 = (move_left (before) (best) (j)))) ,
  TT && emp 
|--
  EX cur : (List Int),
  “ (((move_left (before) (best) (j)) ++ ((0 : Int) :: (@List.nil Int))) = (cur ++ ((0 : Int) :: (@List.nil Int)))) ” &&
  “ ((start_k - (best - j)) <= k_pre) ” &&
  “ ((Zlength (cur)) = (Zlength (digits))) ” &&
  “ forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < (Zlength (digits)))) -> ((48 <= (Znth p_2 cur (0 : Int))) ∧ ((Znth p_2 cur (0 : Int)) <= 57))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (Zlength (digits))) ” &&
  “ (GreedyProgress digits k_pre cur (i + 1) (start_k - (best - j))) ” &&
  “ (GreedySelectionReady cur (i + 1) (start_k - (best - j))) ”
  &&  emp
)

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (k_pre : Int) (i : Int) (cur : (List Int)) (k : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : ((0 : Int) <= k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (cur)) = n_pre)) (PreH9 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH10 : forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57)))) (PreH11 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur (0 : Int))) ∧ ((Znth p_2 cur (0 : Int)) <= 57)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (GreedyProgress digits k_pre cur i k)) (PreH15 : (GreedySelectionReady cur i k)) ,
  (charArray.full d_pre (n_pre + 1) (cur ++ ((0 : Int) :: (@List.nil Int))))
|--
  EX out : (List Int),
  “ (Spec digits k_pre out) ”
  &&  (charArray.full d_pre (n_pre + 1) (out ++ ((0 : Int) :: (@List.nil Int))))
) \/
(
forall (digits : (List Int)) (n_pre : Int) (k_pre : Int) (i : Int) (cur : (List Int)) (k : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : ((0 : Int) <= k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (cur)) = n_pre)) (PreH9 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH10 : forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57)))) (PreH11 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur (0 : Int))) ∧ ((Znth p_2 cur (0 : Int)) <= 57)))) (PreH12 : ((0 : Int) <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (GreedyProgress digits k_pre cur i k)) (PreH15 : (GreedySelectionReady cur i k)) ,
  TT && emp 
|--
  EX out : (List Int),
  “ ((cur ++ ((0 : Int) :: (@List.nil Int))) = (out ++ ((0 : Int) :: (@List.nil Int)))) ” &&
  “ (Spec digits k_pre out) ”
  &&  emp
)

noncomputable def solver_return_wit_2 : Prop :=
  (
forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (k_pre : Int) (i : Int) (cur : (List Int)) (k : Int) (PreH1 : (k <= (0 : Int))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 19)) (PreH5 : ((0 : Int) <= k)) (PreH6 : (k <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (n_pre = (Zlength (digits)))) (PreH9 : ((Zlength (cur)) = n_pre)) (PreH10 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH11 : forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57)))) (PreH12 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur (0 : Int))) ∧ ((Znth p_2 cur (0 : Int)) <= 57)))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (GreedyProgress digits k_pre cur i k)) (PreH16 : (GreedySelectionReady cur i k)) ,
  (charArray.full d_pre (n_pre + 1) (cur ++ ((0 : Int) :: (@List.nil Int))))
|--
  EX out : (List Int),
  “ (Spec digits k_pre out) ”
  &&  (charArray.full d_pre (n_pre + 1) (out ++ ((0 : Int) :: (@List.nil Int))))
) \/
(
forall (digits : (List Int)) (n_pre : Int) (k_pre : Int) (i : Int) (cur : (List Int)) (k : Int) (PreH1 : (k <= (0 : Int))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 19)) (PreH5 : ((0 : Int) <= k)) (PreH6 : (k <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (n_pre = (Zlength (digits)))) (PreH9 : ((Zlength (cur)) = n_pre)) (PreH10 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH11 : forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57)))) (PreH12 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur (0 : Int))) ∧ ((Znth p_2 cur (0 : Int)) <= 57)))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (GreedyProgress digits k_pre cur i k)) (PreH16 : (GreedySelectionReady cur i k)) ,
  TT && emp 
|--
  EX out : (List Int),
  “ ((cur ++ ((0 : Int) :: (@List.nil Int))) = (out ++ ((0 : Int) :: (@List.nil Int)))) ” &&
  “ (Spec digits k_pre out) ”
  &&  emp
)

noncomputable def solver_partial_solve_wit_1 : Prop :=
  forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (k_pre : Int) (best : Int) (j : Int) (i : Int) (cur : (List Int)) (k : Int) (PreH1 : ((j - i) <= k)) (PreH2 : (j < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 19)) (PreH5 : ((0 : Int) < k)) (PreH6 : (k <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (n_pre = (Zlength (digits)))) (PreH9 : ((Zlength (cur)) = n_pre)) (PreH10 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH11 : forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57)))) (PreH12 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur (0 : Int))) ∧ ((Znth p_2 cur (0 : Int)) <= 57)))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((i + 1) <= j)) (PreH16 : (j <= n_pre)) (PreH17 : (j <= ((i + k) + 1))) (PreH18 : (i <= best)) (PreH19 : (best < j)) (PreH20 : (FirstMaximumPrefix cur i j best)) (PreH21 : (GreedyProgress digits k_pre cur i k)) (PreH22 : (GreedySelectionReady cur i k)) ,
  (charArray.full d_pre (n_pre + 1) (cur ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ ((j - i) <= k) ” &&
  “ (j < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 19) ” &&
  “ ((0 : Int) < k) ” &&
  “ (k <= k_pre) ” &&
  “ (k_pre <= 100) ” &&
  “ (n_pre = (Zlength (digits))) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ ((Znth (0 : Int) digits (0 : Int)) ≠ 48) ” &&
  “ forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57))) ” &&
  “ forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur (0 : Int))) ∧ ((Znth p_2 cur (0 : Int)) <= 57))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (j <= ((i + k) + 1)) ” &&
  “ (i <= best) ” &&
  “ (best < j) ” &&
  “ (FirstMaximumPrefix cur i j best) ” &&
  “ (GreedyProgress digits k_pre cur i k) ” &&
  “ (GreedySelectionReady cur i k) ”
  &&  (((d_pre + (j * sizeof(CHAR)))) # Char |-> ((Znth j (cur ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** (charArray.missing_i d_pre j (0 : Int) (n_pre + 1) (cur ++ ((0 : Int) :: (@List.nil Int))))

noncomputable def solver_partial_solve_wit_2 : Prop :=
  forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (k_pre : Int) (best : Int) (j : Int) (i : Int) (cur : (List Int)) (k : Int) (PreH1 : ((j - i) <= k)) (PreH2 : (j < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 19)) (PreH5 : ((0 : Int) < k)) (PreH6 : (k <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (n_pre = (Zlength (digits)))) (PreH9 : ((Zlength (cur)) = n_pre)) (PreH10 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH11 : forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57)))) (PreH12 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur (0 : Int))) ∧ ((Znth p_2 cur (0 : Int)) <= 57)))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((i + 1) <= j)) (PreH16 : (j <= n_pre)) (PreH17 : (j <= ((i + k) + 1))) (PreH18 : (i <= best)) (PreH19 : (best < j)) (PreH20 : (FirstMaximumPrefix cur i j best)) (PreH21 : (GreedyProgress digits k_pre cur i k)) (PreH22 : (GreedySelectionReady cur i k)) ,
  (charArray.full d_pre (n_pre + 1) (cur ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ ((j - i) <= k) ” &&
  “ (j < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 19) ” &&
  “ ((0 : Int) < k) ” &&
  “ (k <= k_pre) ” &&
  “ (k_pre <= 100) ” &&
  “ (n_pre = (Zlength (digits))) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ ((Znth (0 : Int) digits (0 : Int)) ≠ 48) ” &&
  “ forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57))) ” &&
  “ forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 cur (0 : Int))) ∧ ((Znth p_2 cur (0 : Int)) <= 57))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((i + 1) <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (j <= ((i + k) + 1)) ” &&
  “ (i <= best) ” &&
  “ (best < j) ” &&
  “ (FirstMaximumPrefix cur i j best) ” &&
  “ (GreedyProgress digits k_pre cur i k) ” &&
  “ (GreedySelectionReady cur i k) ”
  &&  (((d_pre + (best * sizeof(CHAR)))) # Char |-> ((Znth best (cur ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** (charArray.missing_i d_pre best (0 : Int) (n_pre + 1) (cur ++ ((0 : Int) :: (@List.nil Int))))

noncomputable def solver_partial_solve_wit_3 : Prop :=
  forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (k_pre : Int) (k : Int) (best : Int) (j : Int) (i : Int) (cur : (List Int)) (before : (List Int)) (start_k : Int) (PreH1 : (j > i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : ((0 : Int) < start_k)) (PreH5 : (start_k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (before)) = n_pre)) (PreH9 : ((Zlength (cur)) = n_pre)) (PreH10 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH11 : forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57)))) (PreH12 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before (0 : Int))) ∧ ((Znth p_2 before (0 : Int)) <= 57)))) (PreH13 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur (0 : Int))) ∧ ((Znth p_3 cur (0 : Int)) <= 57)))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= best)) (PreH18 : (best < n_pre)) (PreH19 : ((best - i) <= start_k)) (PreH20 : (k = (start_k - (best - j)))) (PreH21 : ((0 : Int) <= k)) (PreH22 : (k <= start_k)) (PreH23 : (ReachableFirstMaximum before i start_k best)) (PreH24 : (GreedyProgress digits k_pre before i start_k)) (PreH25 : (GreedySelectionReady before i start_k)) (PreH26 : (GreedyExchangeClosure before i start_k best)) (PreH27 : (cur = (move_left (before) (best) (j)))) ,
  (charArray.full d_pre (n_pre + 1) (cur ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ (j > i) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 19) ” &&
  “ ((0 : Int) < start_k) ” &&
  “ (start_k <= k_pre) ” &&
  “ (k_pre <= 100) ” &&
  “ (n_pre = (Zlength (digits))) ” &&
  “ ((Zlength (before)) = n_pre) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ ((Znth (0 : Int) digits (0 : Int)) ≠ 48) ” &&
  “ forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57))) ” &&
  “ forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before (0 : Int))) ∧ ((Znth p_2 before (0 : Int)) <= 57))) ” &&
  “ forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur (0 : Int))) ∧ ((Znth p_3 cur (0 : Int)) <= 57))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (i <= j) ” &&
  “ (j <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((best - i) <= start_k) ” &&
  “ (k = (start_k - (best - j))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= start_k) ” &&
  “ (ReachableFirstMaximum before i start_k best) ” &&
  “ (GreedyProgress digits k_pre before i start_k) ” &&
  “ (GreedySelectionReady before i start_k) ” &&
  “ (GreedyExchangeClosure before i start_k best) ” &&
  “ (cur = (move_left (before) (best) (j))) ”
  &&  (((d_pre + (j * sizeof(CHAR)))) # Char |-> ((Znth j (cur ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** (charArray.missing_i d_pre j (0 : Int) (n_pre + 1) (cur ++ ((0 : Int) :: (@List.nil Int))))

noncomputable def solver_partial_solve_wit_4 : Prop :=
  forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (k_pre : Int) (k : Int) (best : Int) (j : Int) (i : Int) (cur : (List Int)) (before : (List Int)) (start_k : Int) (PreH1 : (j > i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : ((0 : Int) < start_k)) (PreH5 : (start_k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (before)) = n_pre)) (PreH9 : ((Zlength (cur)) = n_pre)) (PreH10 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH11 : forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57)))) (PreH12 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before (0 : Int))) ∧ ((Znth p_2 before (0 : Int)) <= 57)))) (PreH13 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur (0 : Int))) ∧ ((Znth p_3 cur (0 : Int)) <= 57)))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= best)) (PreH18 : (best < n_pre)) (PreH19 : ((best - i) <= start_k)) (PreH20 : (k = (start_k - (best - j)))) (PreH21 : ((0 : Int) <= k)) (PreH22 : (k <= start_k)) (PreH23 : (ReachableFirstMaximum before i start_k best)) (PreH24 : (GreedyProgress digits k_pre before i start_k)) (PreH25 : (GreedySelectionReady before i start_k)) (PreH26 : (GreedyExchangeClosure before i start_k best)) (PreH27 : (cur = (move_left (before) (best) (j)))) ,
  (charArray.full d_pre (n_pre + 1) (cur ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ (j > i) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 19) ” &&
  “ ((0 : Int) < start_k) ” &&
  “ (start_k <= k_pre) ” &&
  “ (k_pre <= 100) ” &&
  “ (n_pre = (Zlength (digits))) ” &&
  “ ((Zlength (before)) = n_pre) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ ((Znth (0 : Int) digits (0 : Int)) ≠ 48) ” &&
  “ forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57))) ” &&
  “ forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before (0 : Int))) ∧ ((Znth p_2 before (0 : Int)) <= 57))) ” &&
  “ forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur (0 : Int))) ∧ ((Znth p_3 cur (0 : Int)) <= 57))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (i <= j) ” &&
  “ (j <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((best - i) <= start_k) ” &&
  “ (k = (start_k - (best - j))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= start_k) ” &&
  “ (ReachableFirstMaximum before i start_k best) ” &&
  “ (GreedyProgress digits k_pre before i start_k) ” &&
  “ (GreedySelectionReady before i start_k) ” &&
  “ (GreedyExchangeClosure before i start_k best) ” &&
  “ (cur = (move_left (before) (best) (j))) ”
  &&  (((d_pre + ((j - 1) * sizeof(CHAR)))) # Char |-> ((Znth (j - 1) (cur ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))))
  ** (charArray.missing_i d_pre (j - 1) (0 : Int) (n_pre + 1) (cur ++ ((0 : Int) :: (@List.nil Int))))

noncomputable def solver_partial_solve_wit_5 : Prop :=
  forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (k_pre : Int) (k : Int) (best : Int) (j : Int) (i : Int) (cur : (List Int)) (before : (List Int)) (start_k : Int) (PreH1 : (j > i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : ((0 : Int) < start_k)) (PreH5 : (start_k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (before)) = n_pre)) (PreH9 : ((Zlength (cur)) = n_pre)) (PreH10 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH11 : forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57)))) (PreH12 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before (0 : Int))) ∧ ((Znth p_2 before (0 : Int)) <= 57)))) (PreH13 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur (0 : Int))) ∧ ((Znth p_3 cur (0 : Int)) <= 57)))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= best)) (PreH18 : (best < n_pre)) (PreH19 : ((best - i) <= start_k)) (PreH20 : (k = (start_k - (best - j)))) (PreH21 : ((0 : Int) <= k)) (PreH22 : (k <= start_k)) (PreH23 : (ReachableFirstMaximum before i start_k best)) (PreH24 : (GreedyProgress digits k_pre before i start_k)) (PreH25 : (GreedySelectionReady before i start_k)) (PreH26 : (GreedyExchangeClosure before i start_k best)) (PreH27 : (cur = (move_left (before) (best) (j)))) ,
  (charArray.full d_pre (n_pre + 1) (cur ++ ((0 : Int) :: (@List.nil Int))))
|--
  “ (j > i) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 19) ” &&
  “ ((0 : Int) < start_k) ” &&
  “ (start_k <= k_pre) ” &&
  “ (k_pre <= 100) ” &&
  “ (n_pre = (Zlength (digits))) ” &&
  “ ((Zlength (before)) = n_pre) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ ((Znth (0 : Int) digits (0 : Int)) ≠ 48) ” &&
  “ forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57))) ” &&
  “ forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before (0 : Int))) ∧ ((Znth p_2 before (0 : Int)) <= 57))) ” &&
  “ forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur (0 : Int))) ∧ ((Znth p_3 cur (0 : Int)) <= 57))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (i <= j) ” &&
  “ (j <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((best - i) <= start_k) ” &&
  “ (k = (start_k - (best - j))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= start_k) ” &&
  “ (ReachableFirstMaximum before i start_k best) ” &&
  “ (GreedyProgress digits k_pre before i start_k) ” &&
  “ (GreedySelectionReady before i start_k) ” &&
  “ (GreedyExchangeClosure before i start_k best) ” &&
  “ (cur = (move_left (before) (best) (j))) ”
  &&  (((d_pre + (j * sizeof(CHAR)))) # Char |->_)
  ** (charArray.missing_i d_pre j (0 : Int) (n_pre + 1) (cur ++ ((0 : Int) :: (@List.nil Int))))

noncomputable def solver_partial_solve_wit_6 : Prop :=
  forall (digits : (List Int)) (d_pre : Int) (n_pre : Int) (k_pre : Int) (k : Int) (best : Int) (j : Int) (i : Int) (cur : (List Int)) (before : (List Int)) (start_k : Int) (PreH1 : (j > i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 19)) (PreH4 : ((0 : Int) < start_k)) (PreH5 : (start_k <= k_pre)) (PreH6 : (k_pre <= 100)) (PreH7 : (n_pre = (Zlength (digits)))) (PreH8 : ((Zlength (before)) = n_pre)) (PreH9 : ((Zlength (cur)) = n_pre)) (PreH10 : ((Znth (0 : Int) digits (0 : Int)) ≠ 48)) (PreH11 : forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57)))) (PreH12 : forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before (0 : Int))) ∧ ((Znth p_2 before (0 : Int)) <= 57)))) (PreH13 : forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur (0 : Int))) ∧ ((Znth p_3 cur (0 : Int)) <= 57)))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : (i <= j)) (PreH17 : (j <= best)) (PreH18 : (best < n_pre)) (PreH19 : ((best - i) <= start_k)) (PreH20 : (k = (start_k - (best - j)))) (PreH21 : ((0 : Int) <= k)) (PreH22 : (k <= start_k)) (PreH23 : (ReachableFirstMaximum before i start_k best)) (PreH24 : (GreedyProgress digits k_pre before i start_k)) (PreH25 : (GreedySelectionReady before i start_k)) (PreH26 : (GreedyExchangeClosure before i start_k best)) (PreH27 : (cur = (move_left (before) (best) (j)))) ,
  (charArray.full d_pre (n_pre + 1) (replace_Znth (j) ((Znth (j - 1) (cur ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))) ((cur ++ ((0 : Int) :: (@List.nil Int))))))
|--
  “ (j > i) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 19) ” &&
  “ ((0 : Int) < start_k) ” &&
  “ (start_k <= k_pre) ” &&
  “ (k_pre <= 100) ” &&
  “ (n_pre = (Zlength (digits))) ” &&
  “ ((Zlength (before)) = n_pre) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ ((Znth (0 : Int) digits (0 : Int)) ≠ 48) ” &&
  “ forall (p : Int) , ((((0 : Int) <= p) ∧ (p < n_pre)) -> ((48 <= (Znth p digits (0 : Int))) ∧ ((Znth p digits (0 : Int)) <= 57))) ” &&
  “ forall (p_2 : Int) , ((((0 : Int) <= p_2) ∧ (p_2 < n_pre)) -> ((48 <= (Znth p_2 before (0 : Int))) ∧ ((Znth p_2 before (0 : Int)) <= 57))) ” &&
  “ forall (p_3 : Int) , ((((0 : Int) <= p_3) ∧ (p_3 < n_pre)) -> ((48 <= (Znth p_3 cur (0 : Int))) ∧ ((Znth p_3 cur (0 : Int)) <= 57))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (i <= j) ” &&
  “ (j <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((best - i) <= start_k) ” &&
  “ (k = (start_k - (best - j))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= start_k) ” &&
  “ (ReachableFirstMaximum before i start_k best) ” &&
  “ (GreedyProgress digits k_pre before i start_k) ” &&
  “ (GreedySelectionReady before i start_k) ” &&
  “ (GreedyExchangeClosure before i start_k best) ” &&
  “ (cur = (move_left (before) (best) (j))) ”
  &&  (((d_pre + ((j - 1) * sizeof(CHAR)))) # Char |->_)
  ** (charArray.missing_i d_pre (j - 1) (0 : Int) (n_pre + 1) (replace_Znth (j) ((Znth (j - 1) (cur ++ ((0 : Int) :: (@List.nil Int))) (0 : Int))) ((cur ++ ((0 : Int) :: (@List.nil Int))))))


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
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2
  proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3
  proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4
  proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5
  proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_2 : solver_entail_wit_2
  proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1
  proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2
  proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1
  proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2
  proof_of_solver_entail_wit_5 : solver_entail_wit_5
  proof_of_solver_entail_wit_6 : solver_entail_wit_6
  proof_of_solver_return_wit_1 : solver_return_wit_1
  proof_of_solver_return_wit_2 : solver_return_wit_2

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_goal
