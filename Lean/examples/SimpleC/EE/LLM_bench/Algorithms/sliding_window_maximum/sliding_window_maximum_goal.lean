import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.sliding_window_maximum.sliding_window_maximum_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.sliding_window_maximum.sliding_window_maximum_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance sliding_window_maximum_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def maxSlidingWindow_safety_wit_1 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "z" ) )) # Int |->_)
  ** (intArray.undef_full ( &( "q" ) ) 100000)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.undef_full out_pre ((n_pre - k_pre) + 1))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def maxSlidingWindow_safety_wit_2 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (q_init : (List Int)) (z : Int) (PreH1 : (z < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH7 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH8 : ((0 : Int) <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (q_init)) = z)) ,
  ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "z" ) )) # Int |-> (z))
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.undef_full out_pre ((n_pre - k_pre) + 1))
  ** (intArray.seg ( &( "q" ) ) (0 : Int) z q_init)
  ** (intArray.undef_seg ( &( "q" ) ) z n_pre)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def maxSlidingWindow_safety_wit_3 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (q_init : (List Int)) (z : Int) (PreH1 : (z < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH7 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH8 : ((0 : Int) <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (q_init)) = z)) ,
  (intArray.seg ( &( "q" ) ) (0 : Int) (z + 1) (q_init ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "q" ) ) (z + 1) n_pre)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "z" ) )) # Int |-> (z))
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.undef_full out_pre ((n_pre - k_pre) + 1))
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  “ ((z + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (z + 1)) ”

noncomputable def maxSlidingWindow_safety_wit_4 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (q_init : (List Int)) (z : Int) (PreH1 : (z >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH7 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH8 : ((0 : Int) <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (q_init)) = z)) ,
  ((( &( "head" ) )) # Int |->_)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.undef_full out_pre ((n_pre - k_pre) + 1))
  ** (intArray.seg ( &( "q" ) ) (0 : Int) z q_init)
  ** (intArray.undef_seg ( &( "q" ) ) z n_pre)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def maxSlidingWindow_safety_wit_5 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (q_init : (List Int)) (z : Int) (PreH1 : (z >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH7 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH8 : ((0 : Int) <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (q_init)) = z)) ,
  ((( &( "tail" ) )) # Int |->_)
  ** ((( &( "head" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.undef_full out_pre ((n_pre - k_pre) + 1))
  ** (intArray.seg ( &( "q" ) ) (0 : Int) z q_init)
  ** (intArray.undef_seg ( &( "q" ) ) z n_pre)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def maxSlidingWindow_safety_wit_6 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (q_init : (List Int)) (z : Int) (PreH1 : (z >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH7 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH8 : ((0 : Int) <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (q_init)) = z)) ,
  ((( &( "out_idx" ) )) # Int |->_)
  ** ((( &( "tail" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "head" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.undef_full out_pre ((n_pre - k_pre) + 1))
  ** (intArray.seg ( &( "q" ) ) (0 : Int) z q_init)
  ** (intArray.undef_seg ( &( "q" ) ) z n_pre)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def maxSlidingWindow_safety_wit_7 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (q_init : (List Int)) (z : Int) (PreH1 : (z >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH7 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH8 : ((0 : Int) <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (q_init)) = z)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "out_idx" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "tail" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "head" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.undef_full out_pre ((n_pre - k_pre) + 1))
  ** (intArray.seg ( &( "q" ) ) (0 : Int) z q_init)
  ** (intArray.undef_seg ( &( "q" ) ) z n_pre)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def maxSlidingWindow_safety_wit_8 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (out_l : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l : (List Int)) (PreH1 : (head < tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH18 : ((Zlength (out_l)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l)) (PreH20 : (SWMQueueDropLoopState l q_l head tail i k_pre)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l)))) (PreH22 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l)))) ,
  (intArray.full ( &( "q" ) ) n_pre q_l)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** ((( &( "out_idx" ) )) # Int |-> (out_idx))
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  “ ((i - k_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - k_pre)) ”

noncomputable def maxSlidingWindow_safety_wit_9 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (out_l : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l : (List Int)) (PreH1 : ((Znth head q_l (0 : Int)) <= (i - k_pre))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l)) (PreH21 : (SWMQueueDropLoopState l q_l head tail i k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l)))) ,
  (intArray.full ( &( "q" ) ) n_pre q_l)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** ((( &( "out_idx" ) )) # Int |-> (out_idx))
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  “ ((head + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (head + 1)) ”

noncomputable def maxSlidingWindow_safety_wit_10 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (out_l : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l : (List Int)) (PreH1 : (head < tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH18 : ((Zlength (out_l)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l)) (PreH20 : (SWMQueuePendingState l q_l head tail i k_pre)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l)))) (PreH22 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l)))) (PreH23 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l (0 : Int)))) ∧ ((Znth (tail - 1) q_l (0 : Int)) < n_pre)))) ,
  ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** ((( &( "out_idx" ) )) # Int |-> (out_idx))
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full ( &( "q" ) ) n_pre q_l)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  “ ((tail - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (tail - 1)) ”

noncomputable def maxSlidingWindow_safety_wit_11 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (out_l : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l : (List Int)) (PreH1 : (head < tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH18 : ((Zlength (out_l)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l)) (PreH20 : (SWMQueuePendingState l q_l head tail i k_pre)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l)))) (PreH22 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l)))) (PreH23 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l (0 : Int)))) ∧ ((Znth (tail - 1) q_l (0 : Int)) < n_pre)))) ,
  ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** ((( &( "out_idx" ) )) # Int |-> (out_idx))
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full ( &( "q" ) ) n_pre q_l)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def maxSlidingWindow_safety_wit_12 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (out_l : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l : (List Int)) (PreH1 : ((Znth (Znth (tail - 1) q_l (0 : Int)) l (0 : Int)) <= (Znth i l (0 : Int)))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l)) (PreH21 : (SWMQueuePendingState l q_l head tail i k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l)))) (PreH24 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l (0 : Int)))) ∧ ((Znth (tail - 1) q_l (0 : Int)) < n_pre)))) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.full ( &( "q" ) ) n_pre q_l)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** ((( &( "out_idx" ) )) # Int |-> (out_idx))
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  “ ((tail - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (tail - 1)) ”

noncomputable def maxSlidingWindow_safety_wit_13 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (out_l : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l : (List Int)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH18 : ((Zlength (out_l)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l)) (PreH20 : (SWMQueuePendingState l q_l head tail i k_pre)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l)))) (PreH22 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l)))) (PreH23 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l (0 : Int)))) ∧ ((Znth (tail - 1) q_l (0 : Int)) < n_pre)))) ,
  (intArray.full ( &( "q" ) ) n_pre (replace_Znth (tail) (i) (q_l)))
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** ((( &( "out_idx" ) )) # Int |-> (out_idx))
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  “ ((tail + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (tail + 1)) ”

noncomputable def maxSlidingWindow_safety_wit_14 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (out_l : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l : (List Int)) (PreH1 : ((Znth (Znth (tail - 1) q_l (0 : Int)) l (0 : Int)) > (Znth i l (0 : Int)))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l)) (PreH21 : (SWMQueuePendingState l q_l head tail i k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l)))) (PreH24 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l (0 : Int)))) ∧ ((Znth (tail - 1) q_l (0 : Int)) < n_pre)))) ,
  (intArray.full ( &( "q" ) ) n_pre (replace_Znth (tail) (i) (q_l)))
  ** (intArray.full nums_pre n_pre l)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** ((( &( "out_idx" ) )) # Int |-> (out_idx))
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  “ ((tail + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (tail + 1)) ”

noncomputable def maxSlidingWindow_safety_wit_15 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (out_l : (List Int)) (q_l : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1))) (PreH11 : ((0 : Int) <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH13 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH14 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH15 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH16 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH17 : ((Zlength (out_l)) = out_idx)) (PreH18 : (SWMOutputPrefix l k_pre out_idx out_l)) (PreH19 : (SWMQueueState l q_l head tail (i + 1) k_pre)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l)))) (PreH21 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l)))) ,
  ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** ((( &( "out_idx" ) )) # Int |-> (out_idx))
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full ( &( "q" ) ) n_pre q_l)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  “ ((k_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k_pre - 1)) ”

noncomputable def maxSlidingWindow_safety_wit_16 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (out_l : (List Int)) (q_l : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1))) (PreH11 : ((0 : Int) <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH13 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH14 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH15 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH16 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH17 : ((Zlength (out_l)) = out_idx)) (PreH18 : (SWMOutputPrefix l k_pre out_idx out_l)) (PreH19 : (SWMQueueState l q_l head tail (i + 1) k_pre)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l)))) (PreH21 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l)))) ,
  ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** ((( &( "out_idx" ) )) # Int |-> (out_idx))
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full ( &( "q" ) ) n_pre q_l)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def maxSlidingWindow_safety_wit_17 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (out_l : (List Int)) (q_l : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1))) (PreH11 : (head < n_pre)) (PreH12 : ((0 : Int) <= (Znth head q_l (0 : Int)))) (PreH13 : ((Znth head q_l (0 : Int)) < n_pre)) (PreH14 : (out_idx = ((i - k_pre) + 1))) (PreH15 : ((0 : Int) <= out_idx)) (PreH16 : (out_idx < ((n_pre - k_pre) + 1))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l)) (PreH21 : (SWMQueueState l q_l head tail (i + 1) k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l)))) (PreH24 : (WindowMaxValue l ((i - k_pre) + 1) (i + 1) (Znth (Znth head q_l (0 : Int)) l (0 : Int)))) ,
  (intArray.seg out_pre (0 : Int) (out_idx + 1) (out_l ++ ((Znth (Znth head q_l (0 : Int)) l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg out_pre (out_idx + 1) ((n_pre - k_pre) + 1))
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.full ( &( "q" ) ) n_pre q_l)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** ((( &( "out_idx" ) )) # Int |-> (out_idx))
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  “ ((out_idx + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (out_idx + 1)) ”

noncomputable def maxSlidingWindow_safety_wit_18 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (out_l : (List Int)) (q_l : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head <= tail)) (PreH10 : (tail <= (i + 1))) (PreH11 : ((0 : Int) <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH13 : (((i + 1) < k_pre) -> (out_idx = (0 : Int)))) (PreH14 : ((k_pre <= (i + 1)) -> (out_idx = (((i + 1) - k_pre) + 1)))) (PreH15 : ((k_pre <= (i + 1)) -> (head < tail))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH18 : ((Zlength (out_l)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l)) (PreH20 : (SWMQueueState l q_l head tail (i + 1) k_pre)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l)))) (PreH22 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l)))) ,
  ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** ((( &( "out_idx" ) )) # Int |-> (out_idx))
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full ( &( "q" ) ) n_pre q_l)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def maxSlidingWindow_entail_wit_1 : Prop :=
  (
forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.undef_full ( &( "q" ) ) 100000)
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.undef_full out_pre ((n_pre - k_pre) + 1))
|--
  EX q_init : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((Zlength (q_init)) = (0 : Int)) ”
  &&  (intArray.full nums_pre n_pre l)
  ** (intArray.undef_full out_pre ((n_pre - k_pre) + 1))
  ** (intArray.seg ( &( "q" ) ) (0 : Int) (0 : Int) q_init)
  ** (intArray.undef_seg ( &( "q" ) ) (0 : Int) n_pre)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
) \/
(
forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.undef_full ( &( "q" ) ) 100000)
|--
  “ ((Zlength ((@List.nil Int))) = (0 : Int)) ”
  &&  (intArray.undef_seg ( &( "q" ) ) (0 : Int) n_pre)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
)

noncomputable def maxSlidingWindow_entail_wit_1_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.undef_full ( &( "q" ) ) 100000)
|--
  “ ((Zlength ((@List.nil Int))) = (0 : Int)) ”

noncomputable def maxSlidingWindow_entail_wit_1_split_goal_spatial : Prop :=
  forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.undef_full ( &( "q" ) ) 100000)
|--
  (intArray.undef_seg ( &( "q" ) ) (0 : Int) n_pre)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)

noncomputable def maxSlidingWindow_entail_wit_2 : Prop :=
  (
forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (q_init_2 : (List Int)) (z : Int) (PreH1 : (z < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH7 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH8 : ((0 : Int) <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (q_init_2)) = z)) ,
  (intArray.seg ( &( "q" ) ) (0 : Int) (z + 1) (q_init_2 ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "q" ) ) (z + 1) n_pre)
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.undef_full out_pre ((n_pre - k_pre) + 1))
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  EX q_init : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ” &&
  “ ((0 : Int) <= (z + 1)) ” &&
  “ ((z + 1) <= n_pre) ” &&
  “ ((Zlength (q_init)) = (z + 1)) ”
  &&  (intArray.full nums_pre n_pre l)
  ** (intArray.undef_full out_pre ((n_pre - k_pre) + 1))
  ** (intArray.seg ( &( "q" ) ) (0 : Int) (z + 1) q_init)
  ** (intArray.undef_seg ( &( "q" ) ) (z + 1) n_pre)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
) \/
(
forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (q_init_2 : (List Int)) (z : Int) (PreH1 : (z < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH7 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH8 : ((0 : Int) <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (q_init_2)) = z)) ,
  TT && emp 
|--
  “ ((Zlength ((q_init_2 ++ ((0 : Int) :: (@List.nil Int))))) = (z + 1)) ”
  &&  emp
)

noncomputable def maxSlidingWindow_entail_wit_2_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (q_init_2 : (List Int)) (z : Int) (PreH1 : (z < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH7 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH8 : ((0 : Int) <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (q_init_2)) = z)) ,
  ((Zlength ((q_init_2 ++ ((0 : Int) :: (@List.nil Int))))) = (z + 1))

noncomputable def maxSlidingWindow_entail_wit_3 : Prop :=
  (
forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (q_init : (List Int)) (z : Int) (PreH1 : (z >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH7 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH8 : ((0 : Int) <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (q_init)) = z)) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.undef_full out_pre ((n_pre - k_pre) + 1))
  ** (intArray.seg ( &( "q" ) ) (0 : Int) z q_init)
  ** (intArray.undef_seg ( &( "q" ) ) z n_pre)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  EX out_l : (List Int), EX q_l : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= ((n_pre - k_pre) + 1)) ” &&
  “ (((0 : Int) < k_pre) -> ((0 : Int) = (0 : Int))) ” &&
  “ ((k_pre <= (0 : Int)) -> ((0 : Int) = (((0 : Int) - k_pre) + 1))) ” &&
  “ ((k_pre <= (0 : Int)) -> ((0 : Int) < (0 : Int))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ” &&
  “ ((Zlength (out_l)) = (0 : Int)) ” &&
  “ (SWMOutputPrefix l k_pre (0 : Int) out_l) ” &&
  “ (SWMQueueState l q_l (0 : Int) (0 : Int) (0 : Int) k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist ((0 : Int)) ((0 : Int)) (q_l))) ” &&
  “ (Forall ((GT.gt (α := Int)) (n_pre)) (sublist ((0 : Int)) ((0 : Int)) (q_l))) ”
  &&  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) (0 : Int) out_l)
  ** (intArray.undef_seg out_pre (0 : Int) ((n_pre - k_pre) + 1))
  ** (intArray.full ( &( "q" ) ) n_pre q_l)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
) \/
(
forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (q_init : (List Int)) (z : Int) (PreH1 : (z >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH7 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH8 : ((0 : Int) <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (q_init)) = z)) ,
  TT && emp 
|--
  “ (Forall ((GT.gt (α := Int)) (n_pre)) (sublist ((0 : Int)) ((0 : Int)) (q_init))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist ((0 : Int)) ((0 : Int)) (q_init))) ” &&
  “ (SWMQueueState l q_init (0 : Int) (0 : Int) (0 : Int) k_pre) ” &&
  “ (SWMOutputPrefix l k_pre (0 : Int) (@List.nil Int)) ” &&
  “ ((Zlength ((@List.nil Int))) = (0 : Int)) ”
  &&  emp
)

noncomputable def maxSlidingWindow_entail_wit_3_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (q_init : (List Int)) (z : Int) (PreH1 : (z >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH7 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH8 : ((0 : Int) <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (q_init)) = z)) ,
  (Forall ((GT.gt (α := Int)) (n_pre)) (sublist ((0 : Int)) ((0 : Int)) (q_init)))

noncomputable def maxSlidingWindow_entail_wit_3_split_goal_2 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (q_init : (List Int)) (z : Int) (PreH1 : (z >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH7 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH8 : ((0 : Int) <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (q_init)) = z)) ,
  (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist ((0 : Int)) ((0 : Int)) (q_init)))

noncomputable def maxSlidingWindow_entail_wit_3_split_goal_3 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (q_init : (List Int)) (z : Int) (PreH1 : (z >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH7 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH8 : ((0 : Int) <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (q_init)) = z)) ,
  (SWMQueueState l q_init (0 : Int) (0 : Int) (0 : Int) k_pre)

noncomputable def maxSlidingWindow_entail_wit_3_split_goal_4 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (q_init : (List Int)) (z : Int) (PreH1 : (z >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH7 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH8 : ((0 : Int) <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (q_init)) = z)) ,
  (SWMOutputPrefix l k_pre (0 : Int) (@List.nil Int))

noncomputable def maxSlidingWindow_entail_wit_3_split_goal_5 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (q_init : (List Int)) (z : Int) (PreH1 : (z >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH7 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH8 : ((0 : Int) <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (q_init)) = z)) ,
  ((Zlength ((@List.nil Int))) = (0 : Int))

noncomputable def maxSlidingWindow_entail_wit_4 : Prop :=
  (
forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : ((k_pre <= i) -> (head < tail))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH21 : (SWMQueueState l q_l_2 head tail i k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l_2)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full ( &( "q" ) ) n_pre q_l_2)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  EX out_l : (List Int), EX q_l : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= i) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx <= ((n_pre - k_pre) + 1)) ” &&
  “ ((i < k_pre) -> (out_idx = (0 : Int))) ” &&
  “ ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ” &&
  “ ((Zlength (out_l)) = out_idx) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueueDropLoopState l q_l head tail i k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l))) ” &&
  “ (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l))) ”
  &&  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full ( &( "q" ) ) n_pre q_l)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
) \/
(
forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : ((k_pre <= i) -> (head < tail))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH21 : (SWMQueueState l q_l_2 head tail i k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) ,
  TT && emp 
|--
  “ (SWMQueueDropLoopState l q_l_2 head tail i k_pre) ”
  &&  emp
)

noncomputable def maxSlidingWindow_entail_wit_4_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : ((k_pre <= i) -> (head < tail))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH21 : (SWMQueueState l q_l_2 head tail i k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) ,
  (SWMQueueDropLoopState l q_l_2 head tail i k_pre)

noncomputable def maxSlidingWindow_entail_wit_5 : Prop :=
  (
forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth head q_l_2 (0 : Int)) <= (i - k_pre))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH21 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) ,
  (intArray.full ( &( "q" ) ) n_pre q_l_2)
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l_2)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  EX out_l : (List Int), EX q_l : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= (head + 1)) ” &&
  “ ((head + 1) <= tail) ” &&
  “ (tail <= i) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx <= ((n_pre - k_pre) + 1)) ” &&
  “ ((i < k_pre) -> (out_idx = (0 : Int))) ” &&
  “ ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ” &&
  “ ((Zlength (out_l)) = out_idx) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueueDropLoopState l q_l (head + 1) tail i k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist ((head + 1)) (tail) (q_l))) ” &&
  “ (Forall ((GT.gt (α := Int)) (n_pre)) (sublist ((head + 1)) (tail) (q_l))) ”
  &&  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full ( &( "q" ) ) n_pre q_l)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
) \/
(
forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth head q_l_2 (0 : Int)) <= (i - k_pre))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH21 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) ,
  TT && emp 
|--
  “ (Forall ((GT.gt (α := Int)) (n_pre)) (sublist ((head + 1)) (tail) (q_l_2))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist ((head + 1)) (tail) (q_l_2))) ” &&
  “ (SWMQueueDropLoopState l q_l_2 (head + 1) tail i k_pre) ”
  &&  emp
)

noncomputable def maxSlidingWindow_entail_wit_5_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth head q_l_2 (0 : Int)) <= (i - k_pre))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH21 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) ,
  (Forall ((GT.gt (α := Int)) (n_pre)) (sublist ((head + 1)) (tail) (q_l_2)))

noncomputable def maxSlidingWindow_entail_wit_5_split_goal_2 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth head q_l_2 (0 : Int)) <= (i - k_pre))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH21 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) ,
  (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist ((head + 1)) (tail) (q_l_2)))

noncomputable def maxSlidingWindow_entail_wit_5_split_goal_3 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth head q_l_2 (0 : Int)) <= (i - k_pre))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH21 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) ,
  (SWMQueueDropLoopState l q_l_2 (head + 1) tail i k_pre)

noncomputable def maxSlidingWindow_entail_wit_6_1 : Prop :=
  (
forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH18 : ((Zlength (out_l_2)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH22 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l_2)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full ( &( "q" ) ) n_pre q_l_2)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  EX out_l : (List Int), EX q_l : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= i) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx <= ((n_pre - k_pre) + 1)) ” &&
  “ ((i < k_pre) -> (out_idx = (0 : Int))) ” &&
  “ ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ” &&
  “ ((Zlength (out_l)) = out_idx) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueuePendingState l q_l head tail i k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l))) ” &&
  “ (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l))) ” &&
  “ ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l (0 : Int)))) ∧ ((Znth (tail - 1) q_l (0 : Int)) < n_pre))) ”
  &&  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full ( &( "q" ) ) n_pre q_l)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
) \/
(
forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH18 : ((Zlength (out_l_2)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH22 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) ,
  TT && emp 
|--
  “ (SWMQueuePendingState l q_l_2 head tail i k_pre) ”
  &&  emp
)

noncomputable def maxSlidingWindow_entail_wit_6_1_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH18 : ((Zlength (out_l_2)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH22 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) ,
  (SWMQueuePendingState l q_l_2 head tail i k_pre)

noncomputable def maxSlidingWindow_entail_wit_6_2 : Prop :=
  (
forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth head q_l_2 (0 : Int)) > (i - k_pre))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH21 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) ,
  (intArray.full ( &( "q" ) ) n_pre q_l_2)
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l_2)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  EX out_l : (List Int), EX q_l : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= i) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx <= ((n_pre - k_pre) + 1)) ” &&
  “ ((i < k_pre) -> (out_idx = (0 : Int))) ” &&
  “ ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ” &&
  “ ((Zlength (out_l)) = out_idx) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueuePendingState l q_l head tail i k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l))) ” &&
  “ (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l))) ” &&
  “ ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l (0 : Int)))) ∧ ((Znth (tail - 1) q_l (0 : Int)) < n_pre))) ”
  &&  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full ( &( "q" ) ) n_pre q_l)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
) \/
(
forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth head q_l_2 (0 : Int)) > (i - k_pre))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH21 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) ,
  TT && emp 
|--
  “ ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre))) ” &&
  “ (SWMQueuePendingState l q_l_2 head tail i k_pre) ”
  &&  emp
)

noncomputable def maxSlidingWindow_entail_wit_6_2_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth head q_l_2 (0 : Int)) > (i - k_pre))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH21 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) ,
  ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))

noncomputable def maxSlidingWindow_entail_wit_6_2_split_goal_2 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth head q_l_2 (0 : Int)) > (i - k_pre))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH21 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) ,
  (SWMQueuePendingState l q_l_2 head tail i k_pre)

noncomputable def maxSlidingWindow_entail_wit_7 : Prop :=
  (
forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth (Znth (tail - 1) q_l_2 (0 : Int)) l (0 : Int)) <= (Znth i l (0 : Int)))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH21 : (SWMQueuePendingState l q_l_2 head tail i k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) (PreH24 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.full ( &( "q" ) ) n_pre q_l_2)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l_2)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  EX out_l : (List Int), EX q_l : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= (tail - 1)) ” &&
  “ ((tail - 1) <= i) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx <= ((n_pre - k_pre) + 1)) ” &&
  “ ((i < k_pre) -> (out_idx = (0 : Int))) ” &&
  “ ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ” &&
  “ ((Zlength (out_l)) = out_idx) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueuePendingState l q_l head (tail - 1) i k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) ((tail - 1)) (q_l))) ” &&
  “ (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) ((tail - 1)) (q_l))) ” &&
  “ ((head < (tail - 1)) -> (((((0 : Int) <= ((tail - 1) - 1)) ∧ (((tail - 1) - 1) < n_pre)) ∧ ((0 : Int) <= (Znth ((tail - 1) - 1) q_l (0 : Int)))) ∧ ((Znth ((tail - 1) - 1) q_l (0 : Int)) < n_pre))) ”
  &&  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full ( &( "q" ) ) n_pre q_l)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
) \/
(
forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth (Znth (tail - 1) q_l_2 (0 : Int)) l (0 : Int)) <= (Znth i l (0 : Int)))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH21 : (SWMQueuePendingState l q_l_2 head tail i k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) (PreH24 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) ,
  TT && emp 
|--
  “ ((head < (tail - 1)) -> (((((0 : Int) <= ((tail - 1) - 1)) ∧ (((tail - 1) - 1) < n_pre)) ∧ ((0 : Int) <= (Znth ((tail - 1) - 1) q_l_2 (0 : Int)))) ∧ ((Znth ((tail - 1) - 1) q_l_2 (0 : Int)) < n_pre))) ” &&
  “ (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) ((tail - 1)) (q_l_2))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) ((tail - 1)) (q_l_2))) ” &&
  “ (SWMQueuePendingState l q_l_2 head (tail - 1) i k_pre) ”
  &&  emp
)

noncomputable def maxSlidingWindow_entail_wit_7_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth (Znth (tail - 1) q_l_2 (0 : Int)) l (0 : Int)) <= (Znth i l (0 : Int)))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH21 : (SWMQueuePendingState l q_l_2 head tail i k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) (PreH24 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) ,
  ((head < (tail - 1)) -> (((((0 : Int) <= ((tail - 1) - 1)) ∧ (((tail - 1) - 1) < n_pre)) ∧ ((0 : Int) <= (Znth ((tail - 1) - 1) q_l_2 (0 : Int)))) ∧ ((Znth ((tail - 1) - 1) q_l_2 (0 : Int)) < n_pre)))

noncomputable def maxSlidingWindow_entail_wit_7_split_goal_2 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth (Znth (tail - 1) q_l_2 (0 : Int)) l (0 : Int)) <= (Znth i l (0 : Int)))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH21 : (SWMQueuePendingState l q_l_2 head tail i k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) (PreH24 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) ,
  (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) ((tail - 1)) (q_l_2)))

noncomputable def maxSlidingWindow_entail_wit_7_split_goal_3 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth (Znth (tail - 1) q_l_2 (0 : Int)) l (0 : Int)) <= (Znth i l (0 : Int)))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH21 : (SWMQueuePendingState l q_l_2 head tail i k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) (PreH24 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) ,
  (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) ((tail - 1)) (q_l_2)))

noncomputable def maxSlidingWindow_entail_wit_7_split_goal_4 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth (Znth (tail - 1) q_l_2 (0 : Int)) l (0 : Int)) <= (Znth i l (0 : Int)))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH21 : (SWMQueuePendingState l q_l_2 head tail i k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) (PreH24 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) ,
  (SWMQueuePendingState l q_l_2 head (tail - 1) i k_pre)

noncomputable def maxSlidingWindow_entail_wit_8_1 : Prop :=
  (
forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH18 : ((Zlength (out_l_2)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueuePendingState l q_l_2 head tail i k_pre)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH22 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) (PreH23 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) ,
  (intArray.full ( &( "q" ) ) n_pre (replace_Znth (tail) (i) (q_l_2)))
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l_2)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  EX out_l : (List Int), EX q_l : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head < (tail + 1)) ” &&
  “ ((tail + 1) <= (i + 1)) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx <= ((n_pre - k_pre) + 1)) ” &&
  “ ((i < k_pre) -> (out_idx = (0 : Int))) ” &&
  “ ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ” &&
  “ ((Zlength (out_l)) = out_idx) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueueState l q_l head (tail + 1) (i + 1) k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) ((tail + 1)) (q_l))) ” &&
  “ (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) ((tail + 1)) (q_l))) ”
  &&  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full ( &( "q" ) ) n_pre q_l)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
) \/
(
forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH18 : ((Zlength (out_l_2)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueuePendingState l q_l_2 head tail i k_pre)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH22 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) (PreH23 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) ,
  TT && emp 
|--
  “ (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) ((tail + 1)) ((replace_Znth (tail) (i) (q_l_2))))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) ((tail + 1)) ((replace_Znth (tail) (i) (q_l_2))))) ” &&
  “ (SWMQueueState l (replace_Znth (tail) (i) (q_l_2)) head (tail + 1) (i + 1) k_pre) ” &&
  “ ((Zlength ((replace_Znth (tail) (i) (q_l_2)))) = n_pre) ”
  &&  emp
)

noncomputable def maxSlidingWindow_entail_wit_8_1_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH18 : ((Zlength (out_l_2)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueuePendingState l q_l_2 head tail i k_pre)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH22 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) (PreH23 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) ,
  (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) ((tail + 1)) ((replace_Znth (tail) (i) (q_l_2)))))

noncomputable def maxSlidingWindow_entail_wit_8_1_split_goal_2 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH18 : ((Zlength (out_l_2)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueuePendingState l q_l_2 head tail i k_pre)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH22 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) (PreH23 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) ,
  (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) ((tail + 1)) ((replace_Znth (tail) (i) (q_l_2)))))

noncomputable def maxSlidingWindow_entail_wit_8_1_split_goal_3 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH18 : ((Zlength (out_l_2)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueuePendingState l q_l_2 head tail i k_pre)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH22 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) (PreH23 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) ,
  (SWMQueueState l (replace_Znth (tail) (i) (q_l_2)) head (tail + 1) (i + 1) k_pre)

noncomputable def maxSlidingWindow_entail_wit_8_1_split_goal_4 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH18 : ((Zlength (out_l_2)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueuePendingState l q_l_2 head tail i k_pre)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH22 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) (PreH23 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) ,
  ((Zlength ((replace_Znth (tail) (i) (q_l_2)))) = n_pre)

noncomputable def maxSlidingWindow_entail_wit_8_2 : Prop :=
  (
forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth (Znth (tail - 1) q_l_2 (0 : Int)) l (0 : Int)) > (Znth i l (0 : Int)))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH21 : (SWMQueuePendingState l q_l_2 head tail i k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) (PreH24 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) ,
  (intArray.full ( &( "q" ) ) n_pre (replace_Znth (tail) (i) (q_l_2)))
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l_2)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  EX out_l : (List Int), EX q_l : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head < (tail + 1)) ” &&
  “ ((tail + 1) <= (i + 1)) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx <= ((n_pre - k_pre) + 1)) ” &&
  “ ((i < k_pre) -> (out_idx = (0 : Int))) ” &&
  “ ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ” &&
  “ ((Zlength (out_l)) = out_idx) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueueState l q_l head (tail + 1) (i + 1) k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) ((tail + 1)) (q_l))) ” &&
  “ (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) ((tail + 1)) (q_l))) ”
  &&  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full ( &( "q" ) ) n_pre q_l)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
) \/
(
forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth (Znth (tail - 1) q_l_2 (0 : Int)) l (0 : Int)) > (Znth i l (0 : Int)))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH21 : (SWMQueuePendingState l q_l_2 head tail i k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) (PreH24 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) ,
  TT && emp 
|--
  “ (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) ((tail + 1)) ((replace_Znth (tail) (i) (q_l_2))))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) ((tail + 1)) ((replace_Znth (tail) (i) (q_l_2))))) ” &&
  “ (SWMQueueState l (replace_Znth (tail) (i) (q_l_2)) head (tail + 1) (i + 1) k_pre) ” &&
  “ ((Zlength ((replace_Znth (tail) (i) (q_l_2)))) = n_pre) ”
  &&  emp
)

noncomputable def maxSlidingWindow_entail_wit_8_2_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth (Znth (tail - 1) q_l_2 (0 : Int)) l (0 : Int)) > (Znth i l (0 : Int)))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH21 : (SWMQueuePendingState l q_l_2 head tail i k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) (PreH24 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) ,
  (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) ((tail + 1)) ((replace_Znth (tail) (i) (q_l_2)))))

noncomputable def maxSlidingWindow_entail_wit_8_2_split_goal_2 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth (Znth (tail - 1) q_l_2 (0 : Int)) l (0 : Int)) > (Znth i l (0 : Int)))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH21 : (SWMQueuePendingState l q_l_2 head tail i k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) (PreH24 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) ,
  (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) ((tail + 1)) ((replace_Znth (tail) (i) (q_l_2)))))

noncomputable def maxSlidingWindow_entail_wit_8_2_split_goal_3 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth (Znth (tail - 1) q_l_2 (0 : Int)) l (0 : Int)) > (Znth i l (0 : Int)))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH21 : (SWMQueuePendingState l q_l_2 head tail i k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) (PreH24 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) ,
  (SWMQueueState l (replace_Znth (tail) (i) (q_l_2)) head (tail + 1) (i + 1) k_pre)

noncomputable def maxSlidingWindow_entail_wit_8_2_split_goal_4 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l_2 : (List Int)) (PreH1 : ((Znth (Znth (tail - 1) q_l_2 (0 : Int)) l (0 : Int)) > (Znth i l (0 : Int)))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH21 : (SWMQueuePendingState l q_l_2 head tail i k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) (PreH24 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l_2 (0 : Int)))) ∧ ((Znth (tail - 1) q_l_2 (0 : Int)) < n_pre)))) ,
  ((Zlength ((replace_Znth (tail) (i) (q_l_2)))) = n_pre)

noncomputable def maxSlidingWindow_entail_wit_9 : Prop :=
  (
forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (i >= (k_pre - 1))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head < tail)) (PreH11 : (tail <= (i + 1))) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH18 : ((Zlength (out_l_2)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueState l q_l_2 head tail (i + 1) k_pre)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH22 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l_2)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full ( &( "q" ) ) n_pre q_l_2)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  EX out_l : (List Int), EX q_l : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head < tail) ” &&
  “ (tail <= (i + 1)) ” &&
  “ (head < n_pre) ” &&
  “ ((0 : Int) <= (Znth head q_l (0 : Int))) ” &&
  “ ((Znth head q_l (0 : Int)) < n_pre) ” &&
  “ (out_idx = ((i - k_pre) + 1)) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx < ((n_pre - k_pre) + 1)) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ” &&
  “ ((Zlength (out_l)) = out_idx) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueueState l q_l head tail (i + 1) k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l))) ” &&
  “ (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l))) ” &&
  “ (WindowMaxValue l ((i - k_pre) + 1) (i + 1) (Znth (Znth head q_l (0 : Int)) l (0 : Int))) ”
  &&  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full ( &( "q" ) ) n_pre q_l)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
) \/
(
forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (i >= (k_pre - 1))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head < tail)) (PreH11 : (tail <= (i + 1))) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH18 : ((Zlength (out_l_2)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueState l q_l_2 head tail (i + 1) k_pre)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH22 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) ,
  TT && emp 
|--
  “ (WindowMaxValue l ((i - k_pre) + 1) (i + 1) (Znth (Znth head q_l_2 (0 : Int)) l (0 : Int))) ” &&
  “ ((Znth head q_l_2 (0 : Int)) < n_pre) ” &&
  “ ((0 : Int) <= (Znth head q_l_2 (0 : Int))) ”
  &&  emp
)

noncomputable def maxSlidingWindow_entail_wit_9_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (i >= (k_pre - 1))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head < tail)) (PreH11 : (tail <= (i + 1))) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH18 : ((Zlength (out_l_2)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueState l q_l_2 head tail (i + 1) k_pre)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH22 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) ,
  (WindowMaxValue l ((i - k_pre) + 1) (i + 1) (Znth (Znth head q_l_2 (0 : Int)) l (0 : Int)))

noncomputable def maxSlidingWindow_entail_wit_9_split_goal_2 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (i >= (k_pre - 1))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head < tail)) (PreH11 : (tail <= (i + 1))) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH18 : ((Zlength (out_l_2)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueState l q_l_2 head tail (i + 1) k_pre)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH22 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) ,
  ((Znth head q_l_2 (0 : Int)) < n_pre)

noncomputable def maxSlidingWindow_entail_wit_9_split_goal_3 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (i >= (k_pre - 1))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head < tail)) (PreH11 : (tail <= (i + 1))) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH18 : ((Zlength (out_l_2)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueState l q_l_2 head tail (i + 1) k_pre)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH22 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) ,
  ((0 : Int) <= (Znth head q_l_2 (0 : Int)))

noncomputable def maxSlidingWindow_entail_wit_10_1 : Prop :=
  (
forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1))) (PreH11 : (head < n_pre)) (PreH12 : ((0 : Int) <= (Znth head q_l_2 (0 : Int)))) (PreH13 : ((Znth head q_l_2 (0 : Int)) < n_pre)) (PreH14 : (out_idx = ((i - k_pre) + 1))) (PreH15 : ((0 : Int) <= out_idx)) (PreH16 : (out_idx < ((n_pre - k_pre) + 1))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH21 : (SWMQueueState l q_l_2 head tail (i + 1) k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) (PreH24 : (WindowMaxValue l ((i - k_pre) + 1) (i + 1) (Znth (Znth head q_l_2 (0 : Int)) l (0 : Int)))) ,
  (intArray.seg out_pre (0 : Int) (out_idx + 1) (out_l_2 ++ ((Znth (Znth head q_l_2 (0 : Int)) l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg out_pre (out_idx + 1) ((n_pre - k_pre) + 1))
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.full ( &( "q" ) ) n_pre q_l_2)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  EX out_l : (List Int), EX q_l : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= (i + 1)) ” &&
  “ ((0 : Int) <= (out_idx + 1)) ” &&
  “ ((out_idx + 1) <= ((n_pre - k_pre) + 1)) ” &&
  “ (((i + 1) < k_pre) -> ((out_idx + 1) = (0 : Int))) ” &&
  “ ((k_pre <= (i + 1)) -> ((out_idx + 1) = (((i + 1) - k_pre) + 1))) ” &&
  “ ((k_pre <= (i + 1)) -> (head < tail)) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ” &&
  “ ((Zlength (out_l)) = (out_idx + 1)) ” &&
  “ (SWMOutputPrefix l k_pre (out_idx + 1) out_l) ” &&
  “ (SWMQueueState l q_l head tail (i + 1) k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l))) ” &&
  “ (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l))) ”
  &&  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) (out_idx + 1) out_l)
  ** (intArray.undef_seg out_pre (out_idx + 1) ((n_pre - k_pre) + 1))
  ** (intArray.full ( &( "q" ) ) n_pre q_l)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
) \/
(
forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1))) (PreH11 : (head < n_pre)) (PreH12 : ((0 : Int) <= (Znth head q_l_2 (0 : Int)))) (PreH13 : ((Znth head q_l_2 (0 : Int)) < n_pre)) (PreH14 : (out_idx = ((i - k_pre) + 1))) (PreH15 : ((0 : Int) <= out_idx)) (PreH16 : (out_idx < ((n_pre - k_pre) + 1))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH21 : (SWMQueueState l q_l_2 head tail (i + 1) k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) (PreH24 : (WindowMaxValue l ((i - k_pre) + 1) (i + 1) (Znth (Znth head q_l_2 (0 : Int)) l (0 : Int)))) ,
  TT && emp 
|--
  “ (SWMOutputPrefix l k_pre (((i - k_pre) + 1) + 1) (out_l_2 ++ ((Znth (Znth head q_l_2 (0 : Int)) l (0 : Int)) :: (@List.nil Int)))) ” &&
  “ ((Zlength ((out_l_2 ++ ((Znth (Znth head q_l_2 (0 : Int)) l (0 : Int)) :: (@List.nil Int))))) = (((i - k_pre) + 1) + 1)) ”
  &&  emp
)

noncomputable def maxSlidingWindow_entail_wit_10_1_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1))) (PreH11 : (head < n_pre)) (PreH12 : ((0 : Int) <= (Znth head q_l_2 (0 : Int)))) (PreH13 : ((Znth head q_l_2 (0 : Int)) < n_pre)) (PreH14 : (out_idx = ((i - k_pre) + 1))) (PreH15 : ((0 : Int) <= out_idx)) (PreH16 : (out_idx < ((n_pre - k_pre) + 1))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH21 : (SWMQueueState l q_l_2 head tail (i + 1) k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) (PreH24 : (WindowMaxValue l ((i - k_pre) + 1) (i + 1) (Znth (Znth head q_l_2 (0 : Int)) l (0 : Int)))) ,
  (SWMOutputPrefix l k_pre (((i - k_pre) + 1) + 1) (out_l_2 ++ ((Znth (Znth head q_l_2 (0 : Int)) l (0 : Int)) :: (@List.nil Int))))

noncomputable def maxSlidingWindow_entail_wit_10_1_split_goal_2 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1))) (PreH11 : (head < n_pre)) (PreH12 : ((0 : Int) <= (Znth head q_l_2 (0 : Int)))) (PreH13 : ((Znth head q_l_2 (0 : Int)) < n_pre)) (PreH14 : (out_idx = ((i - k_pre) + 1))) (PreH15 : ((0 : Int) <= out_idx)) (PreH16 : (out_idx < ((n_pre - k_pre) + 1))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH21 : (SWMQueueState l q_l_2 head tail (i + 1) k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) (PreH24 : (WindowMaxValue l ((i - k_pre) + 1) (i + 1) (Znth (Znth head q_l_2 (0 : Int)) l (0 : Int)))) ,
  ((Zlength ((out_l_2 ++ ((Znth (Znth head q_l_2 (0 : Int)) l (0 : Int)) :: (@List.nil Int))))) = (((i - k_pre) + 1) + 1))

noncomputable def maxSlidingWindow_entail_wit_10_2 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (i < (k_pre - 1))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head < tail)) (PreH11 : (tail <= (i + 1))) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH18 : ((Zlength (out_l_2)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueState l q_l_2 head tail (i + 1) k_pre)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH22 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l_2)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full ( &( "q" ) ) n_pre q_l_2)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  EX out_l : (List Int), EX q_l : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= (i + 1)) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx <= ((n_pre - k_pre) + 1)) ” &&
  “ (((i + 1) < k_pre) -> (out_idx = (0 : Int))) ” &&
  “ ((k_pre <= (i + 1)) -> (out_idx = (((i + 1) - k_pre) + 1))) ” &&
  “ ((k_pre <= (i + 1)) -> (head < tail)) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ” &&
  “ ((Zlength (out_l)) = out_idx) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueueState l q_l head tail (i + 1) k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l))) ” &&
  “ (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l))) ”
  &&  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full ( &( "q" ) ) n_pre q_l)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)

noncomputable def maxSlidingWindow_entail_wit_11 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (out_l_2 : (List Int)) (q_l_2 : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head <= tail)) (PreH10 : (tail <= (i + 1))) (PreH11 : ((0 : Int) <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH13 : (((i + 1) < k_pre) -> (out_idx = (0 : Int)))) (PreH14 : ((k_pre <= (i + 1)) -> (out_idx = (((i + 1) - k_pre) + 1)))) (PreH15 : ((k_pre <= (i + 1)) -> (head < tail))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH18 : ((Zlength (out_l_2)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH20 : (SWMQueueState l q_l_2 head tail (i + 1) k_pre)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l_2)))) (PreH22 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l_2)))) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l_2)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full ( &( "q" ) ) n_pre q_l_2)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  EX out_l : (List Int), EX q_l : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= (i + 1)) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx <= ((n_pre - k_pre) + 1)) ” &&
  “ (((i + 1) < k_pre) -> (out_idx = (0 : Int))) ” &&
  “ ((k_pre <= (i + 1)) -> (out_idx = (((i + 1) - k_pre) + 1))) ” &&
  “ ((k_pre <= (i + 1)) -> (head < tail)) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ” &&
  “ ((Zlength (out_l)) = out_idx) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueueState l q_l head tail (i + 1) k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l))) ” &&
  “ (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l))) ”
  &&  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full ( &( "q" ) ) n_pre q_l)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)

noncomputable def maxSlidingWindow_entail_wit_12 : Prop :=
  (
forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : ((k_pre <= i) -> (head < tail))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH21 : (SWMQueueState l q_l head tail i k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l)))) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l_2)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full ( &( "q" ) ) n_pre q_l)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  EX out_l : (List Int),
  “ ((0 : Int) <= head) ” &&
  “ ((0 : Int) <= tail) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (SlidingWindowMaximum l k_pre out_l) ”
  &&  (intArray.full nums_pre n_pre l)
  ** (intArray.full out_pre ((n_pre - k_pre) + 1) out_l)
  ** (intArray.undef_full ( &( "q" ) ) 100000)
) \/
(
forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : ((k_pre <= i) -> (head < tail))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH21 : (SWMQueueState l q_l head tail i k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l)))) ,
  (intArray.full ( &( "q" ) ) n_pre q_l)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  “ (SlidingWindowMaximum l k_pre out_l_2) ”
  &&  (intArray.undef_full ( &( "q" ) ) 100000)
)

noncomputable def maxSlidingWindow_entail_wit_12_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : ((k_pre <= i) -> (head < tail))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH21 : (SWMQueueState l q_l head tail i k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l)))) ,
  (intArray.full ( &( "q" ) ) n_pre q_l)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  “ (SlidingWindowMaximum l k_pre out_l_2) ”

noncomputable def maxSlidingWindow_entail_wit_12_split_goal_spatial : Prop :=
  forall (l : (List Int)) (n_pre : Int) (k_pre : Int) (out_l_2 : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : ((k_pre <= i) -> (head < tail))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2)) (PreH21 : (SWMQueueState l q_l head tail i k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l)))) ,
  (intArray.full ( &( "q" ) ) n_pre q_l)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  (intArray.undef_full ( &( "q" ) ) 100000)

noncomputable def maxSlidingWindow_return_wit_1 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (out_l_2 : (List Int)) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : ((0 : Int) <= head)) (PreH2 : ((0 : Int) <= tail)) (PreH3 : ((0 : Int) <= out_idx)) (PreH4 : (SlidingWindowMaximum l k_pre out_l_2)) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.full out_pre ((n_pre - k_pre) + 1) out_l_2)
|--
  EX out_l : (List Int),
  “ (SlidingWindowMaximum l k_pre out_l) ”
  &&  (intArray.full nums_pre n_pre l)
  ** (intArray.full out_pre ((n_pre - k_pre) + 1) out_l)

noncomputable def maxSlidingWindow_partial_solve_wit_1 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (q_init : (List Int)) (z : Int) (PreH1 : (z < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH7 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH8 : ((0 : Int) <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (q_init)) = z)) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.undef_full out_pre ((n_pre - k_pre) + 1))
  ** (intArray.seg ( &( "q" ) ) (0 : Int) z q_init)
  ** (intArray.undef_seg ( &( "q" ) ) z n_pre)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  “ (z < n_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ” &&
  “ ((0 : Int) <= z) ” &&
  “ (z <= n_pre) ” &&
  “ ((Zlength (q_init)) = z) ”
  &&  (((( &( "q" ) ) + (z * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg ( &( "q" ) ) (z + 1) n_pre)
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.undef_full out_pre ((n_pre - k_pre) + 1))
  ** (intArray.seg ( &( "q" ) ) (0 : Int) z q_init)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)

noncomputable def maxSlidingWindow_partial_solve_wit_2 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (out_l : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l : (List Int)) (PreH1 : (head < tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH18 : ((Zlength (out_l)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l)) (PreH20 : (SWMQueueDropLoopState l q_l head tail i k_pre)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l)))) (PreH22 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l)))) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full ( &( "q" ) ) n_pre q_l)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  “ (head < tail) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= i) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx <= ((n_pre - k_pre) + 1)) ” &&
  “ ((i < k_pre) -> (out_idx = (0 : Int))) ” &&
  “ ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ” &&
  “ ((Zlength (out_l)) = out_idx) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueueDropLoopState l q_l head tail i k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l))) ” &&
  “ (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l))) ”
  &&  (((( &( "q" ) ) + (head * sizeof(INT)))) # Int |-> ((Znth head q_l (0 : Int))))
  ** (intArray.missing_i ( &( "q" ) ) head (0 : Int) n_pre q_l)
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)

noncomputable def maxSlidingWindow_partial_solve_wit_3 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (out_l : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l : (List Int)) (PreH1 : (head < tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH18 : ((Zlength (out_l)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l)) (PreH20 : (SWMQueuePendingState l q_l head tail i k_pre)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l)))) (PreH22 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l)))) (PreH23 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l (0 : Int)))) ∧ ((Znth (tail - 1) q_l (0 : Int)) < n_pre)))) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full ( &( "q" ) ) n_pre q_l)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  “ (head < tail) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= i) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx <= ((n_pre - k_pre) + 1)) ” &&
  “ ((i < k_pre) -> (out_idx = (0 : Int))) ” &&
  “ ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ” &&
  “ ((Zlength (out_l)) = out_idx) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueuePendingState l q_l head tail i k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l))) ” &&
  “ (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l))) ” &&
  “ ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l (0 : Int)))) ∧ ((Znth (tail - 1) q_l (0 : Int)) < n_pre))) ”
  &&  (((( &( "q" ) ) + ((tail - 1) * sizeof(INT)))) # Int |-> ((Znth (tail - 1) q_l (0 : Int))))
  ** (intArray.missing_i ( &( "q" ) ) (tail - 1) (0 : Int) n_pre q_l)
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)

noncomputable def maxSlidingWindow_partial_solve_wit_4 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (out_l : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l : (List Int)) (PreH1 : (head < tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH18 : ((Zlength (out_l)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l)) (PreH20 : (SWMQueuePendingState l q_l head tail i k_pre)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l)))) (PreH22 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l)))) (PreH23 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l (0 : Int)))) ∧ ((Znth (tail - 1) q_l (0 : Int)) < n_pre)))) ,
  (intArray.full ( &( "q" ) ) n_pre q_l)
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  “ (head < tail) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= i) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx <= ((n_pre - k_pre) + 1)) ” &&
  “ ((i < k_pre) -> (out_idx = (0 : Int))) ” &&
  “ ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ” &&
  “ ((Zlength (out_l)) = out_idx) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueuePendingState l q_l head tail i k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l))) ” &&
  “ (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l))) ” &&
  “ ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l (0 : Int)))) ∧ ((Znth (tail - 1) q_l (0 : Int)) < n_pre))) ”
  &&  (((nums_pre + ((Znth (tail - 1) q_l (0 : Int)) * sizeof(INT)))) # Int |-> ((Znth (Znth (tail - 1) q_l (0 : Int)) l (0 : Int))))
  ** (intArray.missing_i nums_pre (Znth (tail - 1) q_l (0 : Int)) (0 : Int) n_pre l)
  ** (intArray.full ( &( "q" ) ) n_pre q_l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)

noncomputable def maxSlidingWindow_partial_solve_wit_5 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (out_l : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l : (List Int)) (PreH1 : (head < tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH18 : ((Zlength (out_l)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l)) (PreH20 : (SWMQueuePendingState l q_l head tail i k_pre)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l)))) (PreH22 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l)))) (PreH23 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l (0 : Int)))) ∧ ((Znth (tail - 1) q_l (0 : Int)) < n_pre)))) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.full ( &( "q" ) ) n_pre q_l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  “ (head < tail) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= i) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx <= ((n_pre - k_pre) + 1)) ” &&
  “ ((i < k_pre) -> (out_idx = (0 : Int))) ” &&
  “ ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ” &&
  “ ((Zlength (out_l)) = out_idx) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueuePendingState l q_l head tail i k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l))) ” &&
  “ (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l))) ” &&
  “ ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l (0 : Int)))) ∧ ((Znth (tail - 1) q_l (0 : Int)) < n_pre))) ”
  &&  (((nums_pre + (i * sizeof(INT)))) # Int |-> ((Znth i l (0 : Int))))
  ** (intArray.missing_i nums_pre i (0 : Int) n_pre l)
  ** (intArray.full ( &( "q" ) ) n_pre q_l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)

noncomputable def maxSlidingWindow_partial_solve_wit_6 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (out_l : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l : (List Int)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : ((0 : Int) <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH14 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH18 : ((Zlength (out_l)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l)) (PreH20 : (SWMQueuePendingState l q_l head tail i k_pre)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l)))) (PreH22 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l)))) (PreH23 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l (0 : Int)))) ∧ ((Znth (tail - 1) q_l (0 : Int)) < n_pre)))) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full ( &( "q" ) ) n_pre q_l)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  “ (head >= tail) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= i) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx <= ((n_pre - k_pre) + 1)) ” &&
  “ ((i < k_pre) -> (out_idx = (0 : Int))) ” &&
  “ ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ” &&
  “ ((Zlength (out_l)) = out_idx) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueuePendingState l q_l head tail i k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l))) ” &&
  “ (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l))) ” &&
  “ ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l (0 : Int)))) ∧ ((Znth (tail - 1) q_l (0 : Int)) < n_pre))) ”
  &&  (((( &( "q" ) ) + (tail * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i ( &( "q" ) ) tail (0 : Int) n_pre q_l)
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)

noncomputable def maxSlidingWindow_partial_solve_wit_7 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (out_l : (List Int)) (out_idx : Int) (tail : Int) (head : Int) (i : Int) (q_l : (List Int)) (PreH1 : ((Znth (Znth (tail - 1) q_l (0 : Int)) l (0 : Int)) > (Znth i l (0 : Int)))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l)) = n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : ((0 : Int) <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre) + 1))) (PreH15 : ((i < k_pre) -> (out_idx = (0 : Int)))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1)))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l)) (PreH21 : (SWMQueuePendingState l q_l head tail i k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l)))) (PreH24 : ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l (0 : Int)))) ∧ ((Znth (tail - 1) q_l (0 : Int)) < n_pre)))) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.full ( &( "q" ) ) n_pre q_l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  “ ((Znth (Znth (tail - 1) q_l (0 : Int)) l (0 : Int)) > (Znth i l (0 : Int))) ” &&
  “ (head < tail) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= i) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx <= ((n_pre - k_pre) + 1)) ” &&
  “ ((i < k_pre) -> (out_idx = (0 : Int))) ” &&
  “ ((k_pre <= i) -> (out_idx = ((i - k_pre) + 1))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ” &&
  “ ((Zlength (out_l)) = out_idx) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueuePendingState l q_l head tail i k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l))) ” &&
  “ (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l))) ” &&
  “ ((head < tail) -> (((((0 : Int) <= (tail - 1)) ∧ ((tail - 1) < n_pre)) ∧ ((0 : Int) <= (Znth (tail - 1) q_l (0 : Int)))) ∧ ((Znth (tail - 1) q_l (0 : Int)) < n_pre))) ”
  &&  (((( &( "q" ) ) + (tail * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i ( &( "q" ) ) tail (0 : Int) n_pre q_l)
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)

noncomputable def maxSlidingWindow_partial_solve_wit_8 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (out_l : (List Int)) (q_l : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1))) (PreH11 : (head < n_pre)) (PreH12 : ((0 : Int) <= (Znth head q_l (0 : Int)))) (PreH13 : ((Znth head q_l (0 : Int)) < n_pre)) (PreH14 : (out_idx = ((i - k_pre) + 1))) (PreH15 : ((0 : Int) <= out_idx)) (PreH16 : (out_idx < ((n_pre - k_pre) + 1))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l)) (PreH21 : (SWMQueueState l q_l head tail (i + 1) k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l)))) (PreH24 : (WindowMaxValue l ((i - k_pre) + 1) (i + 1) (Znth (Znth head q_l (0 : Int)) l (0 : Int)))) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.full ( &( "q" ) ) n_pre q_l)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head < tail) ” &&
  “ (tail <= (i + 1)) ” &&
  “ (head < n_pre) ” &&
  “ ((0 : Int) <= (Znth head q_l (0 : Int))) ” &&
  “ ((Znth head q_l (0 : Int)) < n_pre) ” &&
  “ (out_idx = ((i - k_pre) + 1)) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx < ((n_pre - k_pre) + 1)) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ” &&
  “ ((Zlength (out_l)) = out_idx) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueueState l q_l head tail (i + 1) k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l))) ” &&
  “ (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l))) ” &&
  “ (WindowMaxValue l ((i - k_pre) + 1) (i + 1) (Znth (Znth head q_l (0 : Int)) l (0 : Int))) ”
  &&  (((( &( "q" ) ) + (head * sizeof(INT)))) # Int |-> ((Znth head q_l (0 : Int))))
  ** (intArray.missing_i ( &( "q" ) ) head (0 : Int) n_pre q_l)
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)

noncomputable def maxSlidingWindow_partial_solve_wit_9 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (out_l : (List Int)) (q_l : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1))) (PreH11 : (head < n_pre)) (PreH12 : ((0 : Int) <= (Znth head q_l (0 : Int)))) (PreH13 : ((Znth head q_l (0 : Int)) < n_pre)) (PreH14 : (out_idx = ((i - k_pre) + 1))) (PreH15 : ((0 : Int) <= out_idx)) (PreH16 : (out_idx < ((n_pre - k_pre) + 1))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l)) (PreH21 : (SWMQueueState l q_l head tail (i + 1) k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l)))) (PreH24 : (WindowMaxValue l ((i - k_pre) + 1) (i + 1) (Znth (Znth head q_l (0 : Int)) l (0 : Int)))) ,
  (intArray.full ( &( "q" ) ) n_pre q_l)
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head < tail) ” &&
  “ (tail <= (i + 1)) ” &&
  “ (head < n_pre) ” &&
  “ ((0 : Int) <= (Znth head q_l (0 : Int))) ” &&
  “ ((Znth head q_l (0 : Int)) < n_pre) ” &&
  “ (out_idx = ((i - k_pre) + 1)) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx < ((n_pre - k_pre) + 1)) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ” &&
  “ ((Zlength (out_l)) = out_idx) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueueState l q_l head tail (i + 1) k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l))) ” &&
  “ (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l))) ” &&
  “ (WindowMaxValue l ((i - k_pre) + 1) (i + 1) (Znth (Znth head q_l (0 : Int)) l (0 : Int))) ”
  &&  (((nums_pre + ((Znth head q_l (0 : Int)) * sizeof(INT)))) # Int |-> ((Znth (Znth head q_l (0 : Int)) l (0 : Int))))
  ** (intArray.missing_i nums_pre (Znth head q_l (0 : Int)) (0 : Int) n_pre l)
  ** (intArray.full ( &( "q" ) ) n_pre q_l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)

noncomputable def maxSlidingWindow_partial_solve_wit_10 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (k_pre : Int) (out_pre : Int) (out_l : (List Int)) (q_l : (List Int)) (i : Int) (head : Int) (tail : Int) (out_idx : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l)) = n_pre)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1))) (PreH11 : (head < n_pre)) (PreH12 : ((0 : Int) <= (Znth head q_l (0 : Int)))) (PreH13 : ((Znth head q_l (0 : Int)) < n_pre)) (PreH14 : (out_idx = ((i - k_pre) + 1))) (PreH15 : ((0 : Int) <= out_idx)) (PreH16 : (out_idx < ((n_pre - k_pre) + 1))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) l)) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH19 : ((Zlength (out_l)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l)) (PreH21 : (SWMQueueState l q_l head tail (i + 1) k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l)))) (PreH23 : (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l)))) (PreH24 : (WindowMaxValue l ((i - k_pre) + 1) (i + 1) (Znth (Znth head q_l (0 : Int)) l (0 : Int)))) ,
  (intArray.full nums_pre n_pre l)
  ** (intArray.full ( &( "q" ) ) n_pre q_l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg out_pre out_idx ((n_pre - k_pre) + 1))
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)
|--
  “ (1 <= k_pre) ” &&
  “ (k_pre <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((Zlength (q_l)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head < tail) ” &&
  “ (tail <= (i + 1)) ” &&
  “ (head < n_pre) ” &&
  “ ((0 : Int) <= (Znth head q_l (0 : Int))) ” &&
  “ ((Znth head q_l (0 : Int)) < n_pre) ” &&
  “ (out_idx = ((i - k_pre) + 1)) ” &&
  “ ((0 : Int) <= out_idx) ” &&
  “ (out_idx < ((n_pre - k_pre) + 1)) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ” &&
  “ ((Zlength (out_l)) = out_idx) ” &&
  “ (SWMOutputPrefix l k_pre out_idx out_l) ” &&
  “ (SWMQueueState l q_l head tail (i + 1) k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (sublist (head) (tail) (q_l))) ” &&
  “ (Forall ((GT.gt (α := Int)) (n_pre)) (sublist (head) (tail) (q_l))) ” &&
  “ (WindowMaxValue l ((i - k_pre) + 1) (i + 1) (Znth (Znth head q_l (0 : Int)) l (0 : Int))) ”
  &&  (((out_pre + (out_idx * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg out_pre (out_idx + 1) ((n_pre - k_pre) + 1))
  ** (intArray.full nums_pre n_pre l)
  ** (intArray.full ( &( "q" ) ) n_pre q_l)
  ** (intArray.seg out_pre (0 : Int) out_idx out_l)
  ** (intArray.undef_seg ( &( "q" ) ) n_pre 100000)


structure VC_Correct : Type where
  proof_of_maxSlidingWindow_safety_wit_1 : maxSlidingWindow_safety_wit_1
  proof_of_maxSlidingWindow_safety_wit_2 : maxSlidingWindow_safety_wit_2
  proof_of_maxSlidingWindow_safety_wit_3 : maxSlidingWindow_safety_wit_3
  proof_of_maxSlidingWindow_safety_wit_4 : maxSlidingWindow_safety_wit_4
  proof_of_maxSlidingWindow_safety_wit_5 : maxSlidingWindow_safety_wit_5
  proof_of_maxSlidingWindow_safety_wit_6 : maxSlidingWindow_safety_wit_6
  proof_of_maxSlidingWindow_safety_wit_7 : maxSlidingWindow_safety_wit_7
  proof_of_maxSlidingWindow_safety_wit_8 : maxSlidingWindow_safety_wit_8
  proof_of_maxSlidingWindow_safety_wit_9 : maxSlidingWindow_safety_wit_9
  proof_of_maxSlidingWindow_safety_wit_10 : maxSlidingWindow_safety_wit_10
  proof_of_maxSlidingWindow_safety_wit_11 : maxSlidingWindow_safety_wit_11
  proof_of_maxSlidingWindow_safety_wit_12 : maxSlidingWindow_safety_wit_12
  proof_of_maxSlidingWindow_safety_wit_13 : maxSlidingWindow_safety_wit_13
  proof_of_maxSlidingWindow_safety_wit_14 : maxSlidingWindow_safety_wit_14
  proof_of_maxSlidingWindow_safety_wit_15 : maxSlidingWindow_safety_wit_15
  proof_of_maxSlidingWindow_safety_wit_16 : maxSlidingWindow_safety_wit_16
  proof_of_maxSlidingWindow_safety_wit_17 : maxSlidingWindow_safety_wit_17
  proof_of_maxSlidingWindow_safety_wit_18 : maxSlidingWindow_safety_wit_18
  proof_of_maxSlidingWindow_entail_wit_10_2 : maxSlidingWindow_entail_wit_10_2
  proof_of_maxSlidingWindow_entail_wit_11 : maxSlidingWindow_entail_wit_11
  proof_of_maxSlidingWindow_return_wit_1 : maxSlidingWindow_return_wit_1
  proof_of_maxSlidingWindow_partial_solve_wit_1 : maxSlidingWindow_partial_solve_wit_1
  proof_of_maxSlidingWindow_partial_solve_wit_2 : maxSlidingWindow_partial_solve_wit_2
  proof_of_maxSlidingWindow_partial_solve_wit_3 : maxSlidingWindow_partial_solve_wit_3
  proof_of_maxSlidingWindow_partial_solve_wit_4 : maxSlidingWindow_partial_solve_wit_4
  proof_of_maxSlidingWindow_partial_solve_wit_5 : maxSlidingWindow_partial_solve_wit_5
  proof_of_maxSlidingWindow_partial_solve_wit_6 : maxSlidingWindow_partial_solve_wit_6
  proof_of_maxSlidingWindow_partial_solve_wit_7 : maxSlidingWindow_partial_solve_wit_7
  proof_of_maxSlidingWindow_partial_solve_wit_8 : maxSlidingWindow_partial_solve_wit_8
  proof_of_maxSlidingWindow_partial_solve_wit_9 : maxSlidingWindow_partial_solve_wit_9
  proof_of_maxSlidingWindow_partial_solve_wit_10 : maxSlidingWindow_partial_solve_wit_10
  proof_of_maxSlidingWindow_entail_wit_1 : maxSlidingWindow_entail_wit_1
  proof_of_maxSlidingWindow_entail_wit_2 : maxSlidingWindow_entail_wit_2
  proof_of_maxSlidingWindow_entail_wit_3 : maxSlidingWindow_entail_wit_3
  proof_of_maxSlidingWindow_entail_wit_4 : maxSlidingWindow_entail_wit_4
  proof_of_maxSlidingWindow_entail_wit_5 : maxSlidingWindow_entail_wit_5
  proof_of_maxSlidingWindow_entail_wit_6_1 : maxSlidingWindow_entail_wit_6_1
  proof_of_maxSlidingWindow_entail_wit_6_2 : maxSlidingWindow_entail_wit_6_2
  proof_of_maxSlidingWindow_entail_wit_7 : maxSlidingWindow_entail_wit_7
  proof_of_maxSlidingWindow_entail_wit_8_1 : maxSlidingWindow_entail_wit_8_1
  proof_of_maxSlidingWindow_entail_wit_8_2 : maxSlidingWindow_entail_wit_8_2
  proof_of_maxSlidingWindow_entail_wit_9 : maxSlidingWindow_entail_wit_9
  proof_of_maxSlidingWindow_entail_wit_10_1 : maxSlidingWindow_entail_wit_10_1
  proof_of_maxSlidingWindow_entail_wit_12 : maxSlidingWindow_entail_wit_12

end SimpleC.EE.LLM_bench.Algorithms.sliding_window_maximum.sliding_window_maximum_goal
