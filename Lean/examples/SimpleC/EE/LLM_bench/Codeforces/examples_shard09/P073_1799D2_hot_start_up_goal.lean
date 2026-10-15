import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P073_1799D2_hot_start_up_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P073_1799D2_hot_start_up_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P073_1799D2_hot_start_up_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P073_1799D2_hot_start_up_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 300000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 300000)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i prog (0 : Int))) ∧ ((Znth i prog (0 : Int)) <= k_pre)))) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < k_pre)) -> (((1 <= (Znth i_2 hot_costs (0 : Int))) ∧ ((Znth i_2 hot_costs (0 : Int)) <= (Znth i_2 cold_costs (0 : Int)))) ∧ ((Znth i_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : ((Zlength (hot_costs)) = k_pre)) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.undef_full d_pre (k_pre + 1))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (initialized : (List Int)) (j : Int) (PreH1 : (j <= k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : ((0 : Int) <= j)) (PreH12 : (j <= (k_pre + 1))) (PreH13 : ((Zlength (initialized)) = j)) (PreH14 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 < j)) -> ((Znth q_3 initialized (0 : Int)) = 4557430888798830399))) ,
  (int64Array.seg d_pre (0 : Int) (j + 1) (initialized ++ (4557430888798830399 :: (@List.nil Int))))
  ** (int64Array.undef_seg d_pre (j + 1) (k_pre + 1))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (initialized : (List Int)) (j : Int) (PreH1 : (j <= k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : ((0 : Int) <= j)) (PreH12 : (j <= (k_pre + 1))) (PreH13 : ((Zlength (initialized)) = j)) (PreH14 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 < j)) -> ((Znth q_3 initialized (0 : Int)) = 4557430888798830399))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.seg d_pre (0 : Int) j initialized)
  ** (int64Array.undef_seg d_pre j (k_pre + 1))
|--
  “ (4557430888798830399 <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= 4557430888798830399) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (initialized : (List Int)) (j : Int) (PreH1 : (j > k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : ((0 : Int) <= j)) (PreH12 : (j <= (k_pre + 1))) (PreH13 : ((Zlength (initialized)) = j)) (PreH14 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 < j)) -> ((Znth q_3 initialized (0 : Int)) = 4557430888798830399))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.seg d_pre (0 : Int) j initialized)
  ** (int64Array.undef_seg d_pre j (k_pre + 1))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (initialized : (List Int)) (j : Int) (PreH1 : (j > k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : ((0 : Int) <= j)) (PreH12 : (j <= (k_pre + 1))) (PreH13 : ((Zlength (initialized)) = j)) (PreH14 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 < j)) -> ((Znth q_3 initialized (0 : Int)) = 4557430888798830399))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.seg d_pre (0 : Int) j initialized)
  ** (int64Array.undef_seg d_pre j (k_pre + 1))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (initialized : (List Int)) (j : Int) (PreH1 : (j > k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : ((0 : Int) <= j)) (PreH12 : (j <= (k_pre + 1))) (PreH13 : ((Zlength (initialized)) = j)) (PreH14 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 < j)) -> ((Znth q_3 initialized (0 : Int)) = 4557430888798830399))) ,
  ((( &( "mind" ) )) # Int64 |->_)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "off" ) )) # Int64 |-> ((Znth (Znth (0 : Int) prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  ** (int64Array.full d_pre j (replace_Znth ((0 : Int)) ((0 : Int)) (initialized)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_7 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (initialized : (List Int)) (j : Int) (PreH1 : (j > k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : ((0 : Int) <= j)) (PreH12 : (j <= (k_pre + 1))) (PreH13 : ((Zlength (initialized)) = j)) (PreH14 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 < j)) -> ((Znth q_3 initialized (0 : Int)) = 4557430888798830399))) ,
  ((( &( "off" ) )) # Int64 |->_)
  ** (int64Array.full d_pre j (replace_Znth ((0 : Int)) ((0 : Int)) (initialized)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_8 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (initialized : (List Int)) (j : Int) (PreH1 : (j > k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : ((0 : Int) <= j)) (PreH12 : (j <= (k_pre + 1))) (PreH13 : ((Zlength (initialized)) = j)) (PreH14 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 < j)) -> ((Znth q_3 initialized (0 : Int)) = 4557430888798830399))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "mind" ) )) # Int64 |-> ((0 : Int)))
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "off" ) )) # Int64 |-> ((Znth (Znth (0 : Int) prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  ** (int64Array.full d_pre j (replace_Znth ((0 : Int)) ((0 : Int)) (initialized)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_9 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (dp)) = (k_pre + 1))) (PreH14 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH15 : (i <= off)) (PreH16 : (off <= (i * 1000000000))) (PreH17 : (((-i) * 1000000000) <= mind)) (PreH18 : (mind <= (0 : Int))) (PreH19 : (i <= (mind + off))) (PreH20 : ((mind + off) <= (i * 1000000000))) (PreH21 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH22 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  ((( &( "y" ) )) # Int |->_)
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def solver_safety_wit_10 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (dp)) = (k_pre + 1))) (PreH14 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH15 : (i <= off)) (PreH16 : (off <= (i * 1000000000))) (PreH17 : (((-i) * 1000000000) <= mind)) (PreH18 : (mind <= (0 : Int))) (PreH19 : (i <= (mind + off))) (PreH20 : ((mind + off) <= (i * 1000000000))) (PreH21 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH22 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  ((( &( "y" ) )) # Int |->_)
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_11 : Prop :=
  (
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((Zlength (dp)) = (k_pre + 1))) (PreH15 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH16 : (i <= off)) (PreH17 : (off <= (i * 1000000000))) (PreH18 : (((-i) * 1000000000) <= mind)) (PreH19 : (mind <= (0 : Int))) (PreH20 : (i <= (mind + off))) (PreH21 : ((mind + off) <= (i * 1000000000))) (PreH22 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH23 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |->_)
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
  ** (int64Array.full d_pre (k_pre + 1) dp)
|--
  “ (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) ”
) \/
(
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((Zlength (dp)) = (k_pre + 1))) (PreH15 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH16 : (i <= off)) (PreH17 : (off <= (i * 1000000000))) (PreH18 : (((-i) * 1000000000) <= mind)) (PreH19 : (mind <= (0 : Int))) (PreH20 : (i <= (mind + off))) (PreH21 : ((mind + off) <= (i * 1000000000))) (PreH22 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH23 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |->_)
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
  ** (int64Array.full d_pre (k_pre + 1) dp)
|--
  “ (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) ”
)

noncomputable def solver_safety_wit_11_split_goal_1 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((Zlength (dp)) = (k_pre + 1))) (PreH15 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH16 : (i <= off)) (PreH17 : (off <= (i * 1000000000))) (PreH18 : (((-i) * 1000000000) <= mind)) (PreH19 : (mind <= (0 : Int))) (PreH20 : (i <= (mind + off))) (PreH21 : ((mind + off) <= (i * 1000000000))) (PreH22 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH23 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |->_)
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
  ** (int64Array.full d_pre (k_pre + 1) dp)
|--
  “ (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= 9223372036854775807) ”

noncomputable def solver_safety_wit_11_split_goal_2 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((Zlength (dp)) = (k_pre + 1))) (PreH15 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH16 : (i <= off)) (PreH17 : (off <= (i * 1000000000))) (PreH18 : (((-i) * 1000000000) <= mind)) (PreH19 : (mind <= (0 : Int))) (PreH20 : (i <= (mind + off))) (PreH21 : ((mind + off) <= (i * 1000000000))) (PreH22 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH23 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |->_)
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
  ** (int64Array.full d_pre (k_pre + 1) dp)
|--
  “ ((-9223372036854775808) <= ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) ”

noncomputable def solver_safety_wit_12 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((Zlength (dp)) = (k_pre + 1))) (PreH15 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH16 : (i <= off)) (PreH17 : (off <= (i * 1000000000))) (PreH18 : (((-i) * 1000000000) <= mind)) (PreH19 : (mind <= (0 : Int))) (PreH20 : (i <= (mind + off))) (PreH21 : ((mind + off) <= (i * 1000000000))) (PreH22 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH23 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  ((( &( "candB" ) )) # Int64 |->_)
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
|--
  “ ((mind + off) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (mind + off)) ”

noncomputable def solver_safety_wit_13 : Prop :=
  (
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((Zlength (dp)) = (k_pre + 1))) (PreH15 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH16 : (i <= off)) (PreH17 : (off <= (i * 1000000000))) (PreH18 : (((-i) * 1000000000) <= mind)) (PreH19 : (mind <= (0 : Int))) (PreH20 : (i <= (mind + off))) (PreH21 : ((mind + off) <= (i * 1000000000))) (PreH22 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH23 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |->_)
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
|--
  “ (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) ”
) \/
(
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((Zlength (dp)) = (k_pre + 1))) (PreH15 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH16 : (i <= off)) (PreH17 : (off <= (i * 1000000000))) (PreH18 : (((-i) * 1000000000) <= mind)) (PreH19 : (mind <= (0 : Int))) (PreH20 : (i <= (mind + off))) (PreH21 : ((mind + off) <= (i * 1000000000))) (PreH22 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH23 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |->_)
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
|--
  “ (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) ”
)

noncomputable def solver_safety_wit_13_split_goal_1 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((Zlength (dp)) = (k_pre + 1))) (PreH15 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH16 : (i <= off)) (PreH17 : (off <= (i * 1000000000))) (PreH18 : (((-i) * 1000000000) <= mind)) (PreH19 : (mind <= (0 : Int))) (PreH20 : (i <= (mind + off))) (PreH21 : ((mind + off) <= (i * 1000000000))) (PreH22 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH23 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |->_)
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
|--
  “ (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= 9223372036854775807) ”

noncomputable def solver_safety_wit_13_split_goal_2 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((Zlength (dp)) = (k_pre + 1))) (PreH15 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH16 : (i <= off)) (PreH17 : (off <= (i * 1000000000))) (PreH18 : (((-i) * 1000000000) <= mind)) (PreH19 : (mind <= (0 : Int))) (PreH20 : (i <= (mind + off))) (PreH21 : ((mind + off) <= (i * 1000000000))) (PreH22 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH23 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |->_)
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
|--
  “ ((-9223372036854775808) <= ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) ”

noncomputable def solver_safety_wit_14 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((Zlength (dp)) = (k_pre + 1))) (PreH15 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH16 : (i <= off)) (PreH17 : (off <= (i * 1000000000))) (PreH18 : (((-i) * 1000000000) <= mind)) (PreH19 : (mind <= (0 : Int))) (PreH20 : (i <= (mind + off))) (PreH21 : ((mind + off) <= (i * 1000000000))) (PreH22 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH23 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  ((( &( "candB" ) )) # Int64 |->_)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
|--
  “ ((mind + off) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (mind + off)) ”

noncomputable def solver_safety_wit_15 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((Zlength (dp)) = (k_pre + 1))) (PreH15 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH16 : (i <= off)) (PreH17 : (off <= (i * 1000000000))) (PreH18 : (((-i) * 1000000000) <= mind)) (PreH19 : (mind <= (0 : Int))) (PreH20 : (i <= (mind + off))) (PreH21 : ((mind + off) <= (i * 1000000000))) (PreH22 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH23 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ (4557430888798830399 <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= 4557430888798830399) ”

noncomputable def solver_safety_wit_16 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((Zlength (dp)) = (k_pre + 1))) (PreH15 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH16 : (i <= off)) (PreH17 : (off <= (i * 1000000000))) (PreH18 : (((-i) * 1000000000) <= mind)) (PreH19 : (mind <= (0 : Int))) (PreH20 : (i <= (mind + off))) (PreH21 : ((mind + off) <= (i * 1000000000))) (PreH22 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH23 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  “ (4557430888798830399 <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= 4557430888798830399) ”

noncomputable def solver_safety_wit_17 : Prop :=
  (
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH2 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH12 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1))) (PreH16 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000))) (PreH19 : (((-i) * 1000000000) <= mind)) (PreH20 : (mind <= (0 : Int))) (PreH21 : (i <= (mind + off))) (PreH22 : ((mind + off) <= (i * 1000000000))) (PreH23 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** ((( &( "viaHot" ) )) # Int64 |->_)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) ”
) \/
(
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH2 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH12 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1))) (PreH16 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000))) (PreH19 : (((-i) * 1000000000) <= mind)) (PreH20 : (mind <= (0 : Int))) (PreH21 : (i <= (mind + off))) (PreH22 : ((mind + off) <= (i * 1000000000))) (PreH23 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** ((( &( "viaHot" ) )) # Int64 |->_)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) ”
)

noncomputable def solver_safety_wit_17_split_goal_1 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH2 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH12 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1))) (PreH16 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000))) (PreH19 : (((-i) * 1000000000) <= mind)) (PreH20 : (mind <= (0 : Int))) (PreH21 : (i <= (mind + off))) (PreH22 : ((mind + off) <= (i * 1000000000))) (PreH23 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** ((( &( "viaHot" ) )) # Int64 |->_)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) <= 9223372036854775807) ”

noncomputable def solver_safety_wit_17_split_goal_2 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH2 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH12 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1))) (PreH16 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000))) (PreH19 : (((-i) * 1000000000) <= mind)) (PreH20 : (mind <= (0 : Int))) (PreH21 : (i <= (mind + off))) (PreH22 : ((mind + off) <= (i * 1000000000))) (PreH23 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** ((( &( "viaHot" ) )) # Int64 |->_)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((-9223372036854775808) <= (((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) ”

noncomputable def solver_safety_wit_18 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH2 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH12 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1))) (PreH16 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000))) (PreH19 : (((-i) * 1000000000) <= mind)) (PreH20 : (mind <= (0 : Int))) (PreH21 : (i <= (mind + off))) (PreH22 : ((mind + off) <= (i * 1000000000))) (PreH23 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full d_pre (k_pre + 1) dp)
  ** ((( &( "viaHot" ) )) # Int64 |->_)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ (((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off)) ”

noncomputable def solver_safety_wit_19 : Prop :=
  (
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH2 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH12 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1))) (PreH16 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000))) (PreH19 : (((-i) * 1000000000) <= mind)) (PreH20 : (mind <= (0 : Int))) (PreH21 : (i <= (mind + off))) (PreH22 : ((mind + off) <= (i * 1000000000))) (PreH23 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** ((( &( "viaHot" ) )) # Int64 |->_)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) ”
) \/
(
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH2 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH12 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1))) (PreH16 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000))) (PreH19 : (((-i) * 1000000000) <= mind)) (PreH20 : (mind <= (0 : Int))) (PreH21 : (i <= (mind + off))) (PreH22 : ((mind + off) <= (i * 1000000000))) (PreH23 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** ((( &( "viaHot" ) )) # Int64 |->_)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) ”
)

noncomputable def solver_safety_wit_19_split_goal_1 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH2 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH12 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1))) (PreH16 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000))) (PreH19 : (((-i) * 1000000000) <= mind)) (PreH20 : (mind <= (0 : Int))) (PreH21 : (i <= (mind + off))) (PreH22 : ((mind + off) <= (i * 1000000000))) (PreH23 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** ((( &( "viaHot" ) )) # Int64 |->_)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) <= 9223372036854775807) ”

noncomputable def solver_safety_wit_19_split_goal_2 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH2 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH12 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1))) (PreH16 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000))) (PreH19 : (((-i) * 1000000000) <= mind)) (PreH20 : (mind <= (0 : Int))) (PreH21 : (i <= (mind + off))) (PreH22 : ((mind + off) <= (i * 1000000000))) (PreH23 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** ((( &( "viaHot" ) )) # Int64 |->_)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((-9223372036854775808) <= (((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) ”

noncomputable def solver_safety_wit_20 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH2 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH12 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1))) (PreH16 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000))) (PreH19 : (((-i) * 1000000000) <= mind)) (PreH20 : (mind <= (0 : Int))) (PreH21 : (i <= (mind + off))) (PreH22 : ((mind + off) <= (i * 1000000000))) (PreH23 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full d_pre (k_pre + 1) dp)
  ** ((( &( "viaHot" ) )) # Int64 |->_)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  “ (((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off)) ”

noncomputable def solver_safety_wit_21 : Prop :=
  (
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) ”
) \/
(
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) ”
)

noncomputable def solver_safety_wit_21_split_goal_1 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) <= 9223372036854775807) ”

noncomputable def solver_safety_wit_21_split_goal_2 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((-9223372036854775808) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) ”

noncomputable def solver_safety_wit_22 : Prop :=
  (
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) ”
) \/
(
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) ”
)

noncomputable def solver_safety_wit_22_split_goal_1 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= 9223372036854775807) ”

noncomputable def solver_safety_wit_22_split_goal_2 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((-9223372036854775808) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) ”

noncomputable def solver_safety_wit_23 : Prop :=
  (
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) >= ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) ”
) \/
(
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) >= ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) ”
)

noncomputable def solver_safety_wit_23_split_goal_1 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) >= ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) <= 9223372036854775807) ”

noncomputable def solver_safety_wit_23_split_goal_2 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) >= ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((-9223372036854775808) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) ”

noncomputable def solver_safety_wit_24 : Prop :=
  (
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) >= ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) ”
) \/
(
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) >= ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) ”
)

noncomputable def solver_safety_wit_24_split_goal_1 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) >= ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= 9223372036854775807) ”

noncomputable def solver_safety_wit_24_split_goal_2 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) >= ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((-9223372036854775808) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) ”

noncomputable def solver_safety_wit_25 : Prop :=
  (
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) >= 4557430888798830399)) (PreH2 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH12 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1))) (PreH16 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000))) (PreH19 : (((-i) * 1000000000) <= mind)) (PreH20 : (mind <= (0 : Int))) (PreH21 : (i <= (mind + off))) (PreH22 : ((mind + off) <= (i * 1000000000))) (PreH23 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) ”
) \/
(
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) >= 4557430888798830399)) (PreH2 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH12 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1))) (PreH16 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000))) (PreH19 : (((-i) * 1000000000) <= mind)) (PreH20 : (mind <= (0 : Int))) (PreH21 : (i <= (mind + off))) (PreH22 : ((mind + off) <= (i * 1000000000))) (PreH23 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) ”
)

noncomputable def solver_safety_wit_25_split_goal_1 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) >= 4557430888798830399)) (PreH2 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH12 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1))) (PreH16 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000))) (PreH19 : (((-i) * 1000000000) <= mind)) (PreH20 : (mind <= (0 : Int))) (PreH21 : (i <= (mind + off))) (PreH22 : ((mind + off) <= (i * 1000000000))) (PreH23 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) <= 9223372036854775807) ”

noncomputable def solver_safety_wit_25_split_goal_2 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) >= 4557430888798830399)) (PreH2 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH12 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1))) (PreH16 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000))) (PreH19 : (((-i) * 1000000000) <= mind)) (PreH20 : (mind <= (0 : Int))) (PreH21 : (i <= (mind + off))) (PreH22 : ((mind + off) <= (i * 1000000000))) (PreH23 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((-9223372036854775808) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) ”

noncomputable def solver_safety_wit_26 : Prop :=
  (
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) >= 4557430888798830399)) (PreH2 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH12 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1))) (PreH16 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000))) (PreH19 : (((-i) * 1000000000) <= mind)) (PreH20 : (mind <= (0 : Int))) (PreH21 : (i <= (mind + off))) (PreH22 : ((mind + off) <= (i * 1000000000))) (PreH23 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  “ ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) ”
) \/
(
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) >= 4557430888798830399)) (PreH2 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH12 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1))) (PreH16 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000))) (PreH19 : (((-i) * 1000000000) <= mind)) (PreH20 : (mind <= (0 : Int))) (PreH21 : (i <= (mind + off))) (PreH22 : ((mind + off) <= (i * 1000000000))) (PreH23 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  “ ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) ”
)

noncomputable def solver_safety_wit_26_split_goal_1 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) >= 4557430888798830399)) (PreH2 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH12 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1))) (PreH16 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000))) (PreH19 : (((-i) * 1000000000) <= mind)) (PreH20 : (mind <= (0 : Int))) (PreH21 : (i <= (mind + off))) (PreH22 : ((mind + off) <= (i * 1000000000))) (PreH23 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  “ ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= 9223372036854775807) ”

noncomputable def solver_safety_wit_26_split_goal_2 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) >= 4557430888798830399)) (PreH2 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH12 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1))) (PreH16 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000))) (PreH19 : (((-i) * 1000000000) <= mind)) (PreH20 : (mind <= (0 : Int))) (PreH21 : (i <= (mind + off))) (PreH22 : ((mind + off) <= (i * 1000000000))) (PreH23 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  “ ((-9223372036854775808) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) ”

noncomputable def solver_safety_wit_27 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  ((( &( "ny" ) )) # Int64 |->_)
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ (((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) ”

noncomputable def solver_safety_wit_28 : Prop :=
  (
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  ((( &( "ny" ) )) # Int64 |->_)
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ (((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) ”
) \/
(
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  ((( &( "ny" ) )) # Int64 |->_)
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ (((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) ”
)

noncomputable def solver_safety_wit_28_split_goal_1 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  ((( &( "ny" ) )) # Int64 |->_)
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ (((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) <= 9223372036854775807) ”

noncomputable def solver_safety_wit_28_split_goal_2 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  ((( &( "ny" ) )) # Int64 |->_)
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((-9223372036854775808) <= ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) ”

noncomputable def solver_safety_wit_29 : Prop :=
  (
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) >= ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  ((( &( "ny" ) )) # Int64 |->_)
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) ”
) \/
(
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) >= ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  ((( &( "ny" ) )) # Int64 |->_)
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) ”
)

noncomputable def solver_safety_wit_29_split_goal_1 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) >= ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  ((( &( "ny" ) )) # Int64 |->_)
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) <= 9223372036854775807) ”

noncomputable def solver_safety_wit_29_split_goal_2 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) >= ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  ((( &( "ny" ) )) # Int64 |->_)
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((-9223372036854775808) <= (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) ”

noncomputable def solver_safety_wit_30 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) >= ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  ((( &( "ny" ) )) # Int64 |->_)
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) ”

noncomputable def solver_safety_wit_31 : Prop :=
  (
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) >= 4557430888798830399)) (PreH2 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH12 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1))) (PreH16 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000))) (PreH19 : (((-i) * 1000000000) <= mind)) (PreH20 : (mind <= (0 : Int))) (PreH21 : (i <= (mind + off))) (PreH22 : ((mind + off) <= (i * 1000000000))) (PreH23 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  ((( &( "ny" ) )) # Int64 |->_)
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) ”
) \/
(
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) >= 4557430888798830399)) (PreH2 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH12 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1))) (PreH16 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000))) (PreH19 : (((-i) * 1000000000) <= mind)) (PreH20 : (mind <= (0 : Int))) (PreH21 : (i <= (mind + off))) (PreH22 : ((mind + off) <= (i * 1000000000))) (PreH23 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  ((( &( "ny" ) )) # Int64 |->_)
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) ”
)

noncomputable def solver_safety_wit_31_split_goal_1 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) >= 4557430888798830399)) (PreH2 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH12 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1))) (PreH16 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000))) (PreH19 : (((-i) * 1000000000) <= mind)) (PreH20 : (mind <= (0 : Int))) (PreH21 : (i <= (mind + off))) (PreH22 : ((mind + off) <= (i * 1000000000))) (PreH23 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  ((( &( "ny" ) )) # Int64 |->_)
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) <= 9223372036854775807) ”

noncomputable def solver_safety_wit_31_split_goal_2 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) >= 4557430888798830399)) (PreH2 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH12 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1))) (PreH16 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000))) (PreH19 : (((-i) * 1000000000) <= mind)) (PreH20 : (mind <= (0 : Int))) (PreH21 : (i <= (mind + off))) (PreH22 : ((mind + off) <= (i * 1000000000))) (PreH23 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  ((( &( "ny" ) )) # Int64 |->_)
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
|--
  “ ((-9223372036854775808) <= (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) ”

noncomputable def solver_safety_wit_32 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) >= 4557430888798830399)) (PreH2 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH12 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1))) (PreH16 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000))) (PreH19 : (((-i) * 1000000000) <= mind)) (PreH20 : (mind <= (0 : Int))) (PreH21 : (i <= (mind + off))) (PreH22 : ((mind + off) <= (i * 1000000000))) (PreH23 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  ((( &( "ny" ) )) # Int64 |->_)
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** ((( &( "candB" ) )) # Int64 |-> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** ((( &( "costA" ) )) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  ** (intArray.full a_pre n_pre prog)
  ** ((( &( "y" ) )) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** ((( &( "x" ) )) # Int |-> ((Znth i prog (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  “ ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) ”

noncomputable def solver_safety_wit_33 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny < (Znth y dp (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog (0 : Int)))) (PreH14 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x = y)) (PreH20 : (costA = (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp)) = (k_pre + 1))) (PreH24 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH25 : (i <= (off - costA))) (PreH26 : ((off - costA) <= (i * 1000000000))) (PreH27 : ((i + 1) <= off)) (PreH28 : (off <= ((i + 1) * 1000000000))) (PreH29 : (((-i) * 1000000000) <= mind)) (PreH30 : (mind <= (0 : Int))) (PreH31 : (i <= (mind + (off - costA)))) (PreH32 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH33 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH34 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH35 : (((Znth x dp (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH36 : ((Znth x dp (0 : Int)) < 4557430888798830399)) (PreH37 : (candB = (((Znth x dp (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA) mind)) (PreH43 : (((ny < (Znth y dp (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off ny))) (PreH44 : (((ny < (Znth y dp (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off mind))) (PreH45 : ((ny >= (Znth y dp (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp off mind))) ,
  (int64Array.full d_pre (k_pre + 1) dp)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "y" ) )) # Int |-> (y))
  ** ((( &( "costA" ) )) # Int64 |-> (costA))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
  ** ((( &( "candB" ) )) # Int64 |-> (candB))
  ** ((( &( "ny" ) )) # Int64 |-> (ny))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  “ False ”

noncomputable def solver_safety_wit_34 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny < mind)) (PreH2 : (ny < (Znth y dp (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x ≠ y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA) mind)) (PreH43 : (((ny < (Znth y dp (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off ny))) (PreH44 : (((ny < (Znth y dp (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off mind))) (PreH45 : ((ny >= (Znth y dp (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp off mind))) ,
  (int64Array.full d_pre (k_pre + 1) (replace_Znth (y) (ny) (dp)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "y" ) )) # Int |-> (y))
  ** ((( &( "costA" ) )) # Int64 |-> (costA))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
  ** ((( &( "candB" ) )) # Int64 |-> (candB))
  ** ((( &( "ny" ) )) # Int64 |-> (ny))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  “ False ”

noncomputable def solver_safety_wit_35 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny < mind)) (PreH2 : (ny < (Znth y dp (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x = y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA) mind)) (PreH43 : (((ny < (Znth y dp (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off ny))) (PreH44 : (((ny < (Znth y dp (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off mind))) (PreH45 : ((ny >= (Znth y dp (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp off mind))) ,
  (int64Array.full d_pre (k_pre + 1) (replace_Znth (y) (ny) (dp)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (ny))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_36 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny < mind)) (PreH2 : (ny < (Znth y dp (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x ≠ y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : ((Znth x dp (0 : Int)) < 4557430888798830399)) (PreH38 : (candB = (((Znth x dp (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) (PreH39 : (ny = (candB - off))) (PreH40 : (((-(i + 1)) * 1000000000) <= ny)) (PreH41 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH42 : ((i + 1) <= (ny + off))) (PreH43 : (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA) mind)) (PreH44 : (((ny < (Znth y dp (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off ny))) (PreH45 : (((ny < (Znth y dp (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off mind))) (PreH46 : ((ny >= (Znth y dp (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp off mind))) ,
  (int64Array.full d_pre (k_pre + 1) (replace_Znth (y) (ny) (dp)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (ny))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_37 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x = y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA) mind)) (PreH43 : (((ny < (Znth y dp (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off ny))) (PreH44 : (((ny < (Znth y dp (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off mind))) (PreH45 : ((ny >= (Znth y dp (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp off mind))) ,
  (int64Array.full d_pre (k_pre + 1) (replace_Znth (y) (ny) (dp)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_38 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x ≠ y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA) mind)) (PreH43 : (((ny < (Znth y dp (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off ny))) (PreH44 : (((ny < (Znth y dp (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off mind))) (PreH45 : ((ny >= (Znth y dp (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp off mind))) ,
  (int64Array.full d_pre (k_pre + 1) (replace_Znth (y) (ny) (dp)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_39 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x ≠ y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : ((Znth x dp (0 : Int)) < 4557430888798830399)) (PreH38 : (candB = (((Znth x dp (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) (PreH39 : (ny = (candB - off))) (PreH40 : (((-(i + 1)) * 1000000000) <= ny)) (PreH41 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH42 : ((i + 1) <= (ny + off))) (PreH43 : (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA) mind)) (PreH44 : (((ny < (Znth y dp (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off ny))) (PreH45 : (((ny < (Znth y dp (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off mind))) (PreH46 : ((ny >= (Znth y dp (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp off mind))) ,
  (int64Array.full d_pre (k_pre + 1) (replace_Znth (y) (ny) (dp)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_40 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= (Znth y dp (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog (0 : Int)))) (PreH14 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x = y)) (PreH20 : (costA = (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp)) = (k_pre + 1))) (PreH24 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH25 : (i <= (off - costA))) (PreH26 : ((off - costA) <= (i * 1000000000))) (PreH27 : ((i + 1) <= off)) (PreH28 : (off <= ((i + 1) * 1000000000))) (PreH29 : (((-i) * 1000000000) <= mind)) (PreH30 : (mind <= (0 : Int))) (PreH31 : (i <= (mind + (off - costA)))) (PreH32 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH33 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH34 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH35 : (((Znth x dp (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH36 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH37 : (ny = (candB - off))) (PreH38 : (((-(i + 1)) * 1000000000) <= ny)) (PreH39 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH40 : ((i + 1) <= (ny + off))) (PreH41 : (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA) mind)) (PreH42 : (((ny < (Znth y dp (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off ny))) (PreH43 : (((ny < (Znth y dp (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off mind))) (PreH44 : ((ny >= (Znth y dp (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp off mind))) ,
  (int64Array.full d_pre (k_pre + 1) dp)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_41 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= (Znth y dp (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog (0 : Int)))) (PreH14 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x = y)) (PreH20 : (costA = (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp)) = (k_pre + 1))) (PreH24 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH25 : (i <= (off - costA))) (PreH26 : ((off - costA) <= (i * 1000000000))) (PreH27 : ((i + 1) <= off)) (PreH28 : (off <= ((i + 1) * 1000000000))) (PreH29 : (((-i) * 1000000000) <= mind)) (PreH30 : (mind <= (0 : Int))) (PreH31 : (i <= (mind + (off - costA)))) (PreH32 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH33 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH34 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH35 : (((Znth x dp (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH36 : ((Znth x dp (0 : Int)) < 4557430888798830399)) (PreH37 : (candB = (((Znth x dp (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA) mind)) (PreH43 : (((ny < (Znth y dp (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off ny))) (PreH44 : (((ny < (Znth y dp (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off mind))) (PreH45 : ((ny >= (Znth y dp (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp off mind))) ,
  (int64Array.full d_pre (k_pre + 1) dp)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_42 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= (Znth y dp (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog (0 : Int)))) (PreH14 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x ≠ y)) (PreH20 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp)) = (k_pre + 1))) (PreH24 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH25 : (i <= (off - costA))) (PreH26 : ((off - costA) <= (i * 1000000000))) (PreH27 : ((i + 1) <= off)) (PreH28 : (off <= ((i + 1) * 1000000000))) (PreH29 : (((-i) * 1000000000) <= mind)) (PreH30 : (mind <= (0 : Int))) (PreH31 : (i <= (mind + (off - costA)))) (PreH32 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH33 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH34 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH35 : (((Znth x dp (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH36 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH37 : (ny = (candB - off))) (PreH38 : (((-(i + 1)) * 1000000000) <= ny)) (PreH39 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH40 : ((i + 1) <= (ny + off))) (PreH41 : (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA) mind)) (PreH42 : (((ny < (Znth y dp (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off ny))) (PreH43 : (((ny < (Znth y dp (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off mind))) (PreH44 : ((ny >= (Znth y dp (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp off mind))) ,
  (int64Array.full d_pre (k_pre + 1) dp)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_43 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= (Znth y dp (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog (0 : Int)))) (PreH14 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x ≠ y)) (PreH20 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp)) = (k_pre + 1))) (PreH24 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH25 : (i <= (off - costA))) (PreH26 : ((off - costA) <= (i * 1000000000))) (PreH27 : ((i + 1) <= off)) (PreH28 : (off <= ((i + 1) * 1000000000))) (PreH29 : (((-i) * 1000000000) <= mind)) (PreH30 : (mind <= (0 : Int))) (PreH31 : (i <= (mind + (off - costA)))) (PreH32 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH33 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH34 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH35 : (((Znth x dp (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH36 : ((Znth x dp (0 : Int)) < 4557430888798830399)) (PreH37 : (candB = (((Znth x dp (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA) mind)) (PreH43 : (((ny < (Znth y dp (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off ny))) (PreH44 : (((ny < (Znth y dp (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off mind))) (PreH45 : ((ny >= (Znth y dp (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp off mind))) ,
  (int64Array.full d_pre (k_pre + 1) dp)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_44 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (dp)) = (k_pre + 1))) (PreH14 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH15 : (i <= off)) (PreH16 : (off <= (i * 1000000000))) (PreH17 : (((-i) * 1000000000) <= mind)) (PreH18 : (mind <= (0 : Int))) (PreH19 : (i <= (mind + off))) (PreH20 : ((mind + off) <= (i * 1000000000))) (PreH21 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH22 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "cold" ) )) # Ptr |-> (cold_pre))
  ** ((( &( "hot" ) )) # Ptr |-> (hot_pre))
  ** ((( &( "d" ) )) # Ptr |-> (d_pre))
  ** ((( &( "off" ) )) # Int64 |-> (off))
  ** ((( &( "mind" ) )) # Int64 |-> (mind))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
|--
  “ ((mind + off) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (mind + off)) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 300000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 300000)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i prog (0 : Int))) ∧ ((Znth i prog (0 : Int)) <= k_pre)))) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < k_pre)) -> (((1 <= (Znth i_2 hot_costs (0 : Int))) ∧ ((Znth i_2 hot_costs (0 : Int)) <= (Znth i_2 cold_costs (0 : Int)))) ∧ ((Znth i_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : ((Zlength (hot_costs)) = k_pre)) ,
  (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.undef_full d_pre (k_pre + 1))
|--
  EX initialized : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (k_pre + 1)) ” &&
  “ ((Zlength (initialized)) = (0 : Int)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 < (0 : Int))) -> ((Znth q_3 initialized (0 : Int)) = 4557430888798830399)) ”
  &&  (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.seg d_pre (0 : Int) (0 : Int) initialized)
  ** (int64Array.undef_seg d_pre (0 : Int) (k_pre + 1))
) \/
(
forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 300000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 300000)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i prog (0 : Int))) ∧ ((Znth i prog (0 : Int)) <= k_pre)))) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < k_pre)) -> (((1 <= (Znth i_2 hot_costs (0 : Int))) ∧ ((Znth i_2 hot_costs (0 : Int)) <= (Znth i_2 cold_costs (0 : Int)))) ∧ ((Znth i_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : ((Zlength (hot_costs)) = k_pre)) ,
  TT && emp 
|--
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 < (0 : Int))) -> ((Znth q_3 (@List.nil Int) (0 : Int)) = 4557430888798830399)) ” &&
  “ ((Zlength ((@List.nil Int))) = (0 : Int)) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ”
  &&  emp
)

noncomputable def solver_entail_wit_1_split_goal_1 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 300000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 300000)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i prog (0 : Int))) ∧ ((Znth i prog (0 : Int)) <= k_pre)))) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < k_pre)) -> (((1 <= (Znth i_2 hot_costs (0 : Int))) ∧ ((Znth i_2 hot_costs (0 : Int)) <= (Znth i_2 cold_costs (0 : Int)))) ∧ ((Znth i_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : ((Zlength (hot_costs)) = k_pre)) ,
  forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 < (0 : Int))) -> ((Znth q_3 (@List.nil Int) (0 : Int)) = 4557430888798830399))

noncomputable def solver_entail_wit_1_split_goal_2 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 300000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 300000)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i prog (0 : Int))) ∧ ((Znth i prog (0 : Int)) <= k_pre)))) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < k_pre)) -> (((1 <= (Znth i_2 hot_costs (0 : Int))) ∧ ((Znth i_2 hot_costs (0 : Int)) <= (Znth i_2 cold_costs (0 : Int)))) ∧ ((Znth i_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : ((Zlength (hot_costs)) = k_pre)) ,
  ((Zlength ((@List.nil Int))) = (0 : Int))

noncomputable def solver_entail_wit_1_split_goal_3 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 300000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 300000)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i prog (0 : Int))) ∧ ((Znth i prog (0 : Int)) <= k_pre)))) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < k_pre)) -> (((1 <= (Znth i_2 hot_costs (0 : Int))) ∧ ((Znth i_2 hot_costs (0 : Int)) <= (Znth i_2 cold_costs (0 : Int)))) ∧ ((Znth i_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : ((Zlength (hot_costs)) = k_pre)) ,
  forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))

noncomputable def solver_entail_wit_1_split_goal_4 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 300000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 300000)) (PreH5 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((1 <= (Znth i prog (0 : Int))) ∧ ((Znth i prog (0 : Int)) <= k_pre)))) (PreH6 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < k_pre)) -> (((1 <= (Znth i_2 hot_costs (0 : Int))) ∧ ((Znth i_2 hot_costs (0 : Int)) <= (Znth i_2 cold_costs (0 : Int)))) ∧ ((Znth i_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : ((Zlength (hot_costs)) = k_pre)) ,
  forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))

noncomputable def solver_entail_wit_2 : Prop :=
  (
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (initialized_2 : (List Int)) (j : Int) (PreH1 : (j <= k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : ((0 : Int) <= j)) (PreH12 : (j <= (k_pre + 1))) (PreH13 : ((Zlength (initialized_2)) = j)) (PreH14 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 < j)) -> ((Znth q_3 initialized_2 (0 : Int)) = 4557430888798830399))) ,
  (int64Array.seg d_pre (0 : Int) (j + 1) (initialized_2 ++ (4557430888798830399 :: (@List.nil Int))))
  ** (int64Array.undef_seg d_pre (j + 1) (k_pre + 1))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  EX initialized : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (k_pre + 1)) ” &&
  “ ((Zlength (initialized)) = (j + 1)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 < (j + 1))) -> ((Znth q_3 initialized (0 : Int)) = 4557430888798830399)) ”
  &&  (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.seg d_pre (0 : Int) (j + 1) initialized)
  ** (int64Array.undef_seg d_pre (j + 1) (k_pre + 1))
) \/
(
forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (initialized_2 : (List Int)) (j : Int) (PreH1 : (j <= k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : ((0 : Int) <= j)) (PreH12 : (j <= (k_pre + 1))) (PreH13 : ((Zlength (initialized_2)) = j)) (PreH14 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 < j)) -> ((Znth q_3 initialized_2 (0 : Int)) = 4557430888798830399))) ,
  TT && emp 
|--
  “ ((Zlength ((initialized_2 ++ (4557430888798830399 :: (@List.nil Int))))) = (j + 1)) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_split_goal_1 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (initialized_2 : (List Int)) (j : Int) (PreH1 : (j <= k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : ((0 : Int) <= j)) (PreH12 : (j <= (k_pre + 1))) (PreH13 : ((Zlength (initialized_2)) = j)) (PreH14 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 < j)) -> ((Znth q_3 initialized_2 (0 : Int)) = 4557430888798830399))) ,
  ((Zlength ((initialized_2 ++ (4557430888798830399 :: (@List.nil Int))))) = (j + 1))

noncomputable def solver_entail_wit_3 : Prop :=
  (
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (initialized : (List Int)) (j : Int) (PreH1 : (j > k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : ((0 : Int) <= j)) (PreH12 : (j <= (k_pre + 1))) (PreH13 : ((Zlength (initialized)) = j)) (PreH14 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 < j)) -> ((Znth q_6 initialized (0 : Int)) = 4557430888798830399))) ,
  (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full d_pre j (replace_Znth ((0 : Int)) ((0 : Int)) (initialized)))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  EX dp : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= n_pre) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ (1 <= (Znth (Znth (0 : Int) prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) ” &&
  “ ((Znth (Znth (0 : Int) prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)) <= (1 * 1000000000)) ” &&
  “ (((-1) * 1000000000) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ (1 <= ((0 : Int) + (Znth (Znth (0 : Int) prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) ” &&
  “ (((0 : Int) + (Znth (Znth (0 : Int) prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= (1 * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-1) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (1 * 1000000000))))) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs 1 dp (Znth (Znth (0 : Int) prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)) (0 : Int)) ”
  &&  (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
) \/
(
forall (d_pre : Int) (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (initialized : (List Int)) (j : Int) (PreH1 : (j > k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : ((0 : Int) <= j)) (PreH12 : (j <= (k_pre + 1))) (PreH13 : ((Zlength (initialized)) = j)) (PreH14 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 < j)) -> ((Znth q_6 initialized (0 : Int)) = 4557430888798830399))) ,
  (int64Array.full d_pre j (replace_Znth ((0 : Int)) ((0 : Int)) (initialized)))
|--
  EX dp : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= n_pre) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ (1 <= (Znth (Znth (0 : Int) prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) ” &&
  “ ((Znth (Znth (0 : Int) prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)) <= (1 * 1000000000)) ” &&
  “ (((-1) * 1000000000) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ (1 <= ((0 : Int) + (Znth (Znth (0 : Int) prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) ” &&
  “ (((0 : Int) + (Znth (Znth (0 : Int) prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= (1 * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-1) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (1 * 1000000000))))) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs 1 dp (Znth (Znth (0 : Int) prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)) (0 : Int)) ”
  &&  (int64Array.full d_pre (k_pre + 1) dp)
)

noncomputable def solver_entail_wit_4_1 : Prop :=
  (
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp (0 : Int))) ∧ ((Znth q_6 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (intArray.full a_pre n_pre prog)
|--
  EX dp_2 : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((Znth i prog (0 : Int)) = (Znth i prog (0 : Int))) ” &&
  “ ((Znth (i - 1) prog (0 : Int)) = (Znth (i - 1) prog (0 : Int))) ” &&
  “ (1 <= (Znth i prog (0 : Int))) ” &&
  “ ((Znth i prog (0 : Int)) <= k_pre) ” &&
  “ (1 <= (Znth (i - 1) prog (0 : Int))) ” &&
  “ ((Znth (i - 1) prog (0 : Int)) <= k_pre) ” &&
  “ ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int))) ” &&
  “ ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)) = (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: hot_costs)) ((0 : Int)))) ” &&
  “ (1 <= (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) ” &&
  “ ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)) <= 1000000000) ” &&
  “ ((Zlength (dp_2)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int)) ” &&
  “ (i <= ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) ” &&
  “ (((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) <= (i * 1000000000)) ” &&
  “ ((i + 1) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) ” &&
  “ ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) <= ((i + 1) * 1000000000)) ” &&
  “ (((-i) * 1000000000) <= mind) ” &&
  “ (mind <= (0 : Int)) ” &&
  “ (i <= (mind + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) ” &&
  “ ((mind + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) <= (i * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp_2 (0 : Int))) ∧ ((Znth q_3 dp_2 (0 : Int)) <= (i * 1000000000))))) ” &&
  “ ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) <= ((mind + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) + (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: cold_costs)) ((0 : Int))))) ” &&
  “ (((Znth (Znth i prog (0 : Int)) dp_2 (0 : Int)) < 4557430888798830399) -> ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) <= (((Znth (Znth i prog (0 : Int)) dp_2 (0 : Int)) + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) + (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: hot_costs)) ((0 : Int)))))) ” &&
  “ ((Znth (Znth i prog (0 : Int)) dp_2 (0 : Int)) < 4557430888798830399) ” &&
  “ ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) = (((Znth (Znth i prog (0 : Int)) dp_2 (0 : Int)) + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) + (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: hot_costs)) ((0 : Int))))) ” &&
  “ (((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) = ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) ” &&
  “ (((-(i + 1)) * 1000000000) <= ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) ” &&
  “ ((((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) + (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) <= ((i + 1) * 1000000000)) ” &&
  “ ((i + 1) <= (((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) + (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs i dp_2 ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) mind) ” &&
  “ (((((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) < (Znth (Znth (i - 1) prog (0 : Int)) dp_2 (0 : Int))) ∧ (((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth ((Znth (i - 1) prog (0 : Int))) (((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) (dp_2)) (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))))) ” &&
  “ (((((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) < (Znth (Znth (i - 1) prog (0 : Int)) dp_2 (0 : Int))) ∧ (((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth ((Znth (i - 1) prog (0 : Int))) (((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) (dp_2)) (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) mind)) ” &&
  “ ((((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) >= (Znth (Znth (i - 1) prog (0 : Int)) dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) mind)) ”
  &&  (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp_2)
) \/
(
forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp (0 : Int))) ∧ ((Znth q_6 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  TT && emp 
|--
  “ ((((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) >= (Znth (Znth (i - 1) prog (0 : Int)) dp (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) mind)) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs i dp ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) mind) ” &&
  “ ((i + 1) <= (((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) + (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) ” &&
  “ ((((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) + (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) <= ((i + 1) * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000))))) ” &&
  “ ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) <= ((i + 1) * 1000000000)) ” &&
  “ ((i + 1) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) ” &&
  “ ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)) <= 1000000000) ” &&
  “ (1 <= (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ”
  &&  emp
)

noncomputable def solver_entail_wit_4_1_split_goal_1 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp (0 : Int))) ∧ ((Znth q_6 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  ((((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) >= (Znth (Znth (i - 1) prog (0 : Int)) dp (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) mind))

noncomputable def solver_entail_wit_4_1_split_goal_2 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp (0 : Int))) ∧ ((Znth q_6 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (NormalizedScheduleState prog cold_costs hot_costs i dp ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) mind)

noncomputable def solver_entail_wit_4_1_split_goal_3 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp (0 : Int))) ∧ ((Znth q_6 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  ((i + 1) <= (((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) + (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))))

noncomputable def solver_entail_wit_4_1_split_goal_4 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp (0 : Int))) ∧ ((Znth q_6 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  ((((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) + (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) <= ((i + 1) * 1000000000))

noncomputable def solver_entail_wit_4_1_split_goal_5 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp (0 : Int))) ∧ ((Znth q_6 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))

noncomputable def solver_entail_wit_4_1_split_goal_6 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp (0 : Int))) ∧ ((Znth q_6 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) <= ((i + 1) * 1000000000))

noncomputable def solver_entail_wit_4_1_split_goal_7 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp (0 : Int))) ∧ ((Znth q_6 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  ((i + 1) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))

noncomputable def solver_entail_wit_4_1_split_goal_8 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp (0 : Int))) ∧ ((Znth q_6 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)) <= 1000000000)

noncomputable def solver_entail_wit_4_1_split_goal_9 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp (0 : Int))) ∧ ((Znth q_6 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (1 <= (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))

noncomputable def solver_entail_wit_4_1_split_goal_10 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp (0 : Int))) ∧ ((Znth q_6 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))

noncomputable def solver_entail_wit_4_1_split_goal_11 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp (0 : Int))) ∧ ((Znth q_6 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))

noncomputable def solver_entail_wit_4_2 : Prop :=
  (
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp (0 : Int))) ∧ ((Znth q_6 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (intArray.full a_pre n_pre prog)
|--
  EX dp_2 : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((Znth i prog (0 : Int)) = (Znth i prog (0 : Int))) ” &&
  “ ((Znth (i - 1) prog (0 : Int)) = (Znth (i - 1) prog (0 : Int))) ” &&
  “ (1 <= (Znth i prog (0 : Int))) ” &&
  “ ((Znth i prog (0 : Int)) <= k_pre) ” &&
  “ (1 <= (Znth (i - 1) prog (0 : Int))) ” &&
  “ ((Znth (i - 1) prog (0 : Int)) <= k_pre) ” &&
  “ ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int))) ” &&
  “ ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)) = (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: cold_costs)) ((0 : Int)))) ” &&
  “ (1 <= (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) ” &&
  “ ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)) <= 1000000000) ” &&
  “ ((Zlength (dp_2)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int)) ” &&
  “ (i <= ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) ” &&
  “ (((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= (i * 1000000000)) ” &&
  “ ((i + 1) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) ” &&
  “ ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= ((i + 1) * 1000000000)) ” &&
  “ (((-i) * 1000000000) <= mind) ” &&
  “ (mind <= (0 : Int)) ” &&
  “ (i <= (mind + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) ” &&
  “ ((mind + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) <= (i * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp_2 (0 : Int))) ∧ ((Znth q_3 dp_2 (0 : Int)) <= (i * 1000000000))))) ” &&
  “ ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) <= ((mind + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) + (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: cold_costs)) ((0 : Int))))) ” &&
  “ (((Znth (Znth i prog (0 : Int)) dp_2 (0 : Int)) < 4557430888798830399) -> ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) <= (((Znth (Znth i prog (0 : Int)) dp_2 (0 : Int)) + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) + (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: hot_costs)) ((0 : Int)))))) ” &&
  “ ((Znth (Znth i prog (0 : Int)) dp_2 (0 : Int)) < 4557430888798830399) ” &&
  “ ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) = (((Znth (Znth i prog (0 : Int)) dp_2 (0 : Int)) + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) + (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: hot_costs)) ((0 : Int))))) ” &&
  “ (((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) = ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) ” &&
  “ (((-(i + 1)) * 1000000000) <= ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) ” &&
  “ ((((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) + (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) <= ((i + 1) * 1000000000)) ” &&
  “ ((i + 1) <= (((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) + (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs i dp_2 ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) mind) ” &&
  “ (((((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) < (Znth (Znth (i - 1) prog (0 : Int)) dp_2 (0 : Int))) ∧ (((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth ((Znth (i - 1) prog (0 : Int))) (((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (dp_2)) (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))) ” &&
  “ (((((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) < (Znth (Znth (i - 1) prog (0 : Int)) dp_2 (0 : Int))) ∧ (((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth ((Znth (i - 1) prog (0 : Int))) (((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (dp_2)) (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) mind)) ” &&
  “ ((((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) >= (Znth (Znth (i - 1) prog (0 : Int)) dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) mind)) ”
  &&  (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp_2)
) \/
(
forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp (0 : Int))) ∧ ((Znth q_6 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  TT && emp 
|--
  “ ((((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) >= (Znth (Znth (i - 1) prog (0 : Int)) dp (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) mind)) ” &&
  “ (((((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) < (Znth (Znth (i - 1) prog (0 : Int)) dp (0 : Int))) ∧ (((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth ((Znth (i - 1) prog (0 : Int))) (((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (dp)) (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs i dp ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) mind) ” &&
  “ ((i + 1) <= (((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) + (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) ” &&
  “ ((((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) + (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) <= ((i + 1) * 1000000000)) ” &&
  “ (((-(i + 1)) * 1000000000) <= ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000))))) ” &&
  “ ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= ((i + 1) * 1000000000)) ” &&
  “ ((i + 1) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) ” &&
  “ ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)) <= 1000000000) ” &&
  “ (1 <= (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ”
  &&  emp
)

noncomputable def solver_entail_wit_4_2_split_goal_1 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp (0 : Int))) ∧ ((Znth q_6 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  ((((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) >= (Znth (Znth (i - 1) prog (0 : Int)) dp (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) mind))

noncomputable def solver_entail_wit_4_2_split_goal_2 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp (0 : Int))) ∧ ((Znth q_6 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (((((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) < (Znth (Znth (i - 1) prog (0 : Int)) dp (0 : Int))) ∧ (((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth ((Znth (i - 1) prog (0 : Int))) (((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (dp)) (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))))

noncomputable def solver_entail_wit_4_2_split_goal_3 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp (0 : Int))) ∧ ((Znth q_6 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (NormalizedScheduleState prog cold_costs hot_costs i dp ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) mind)

noncomputable def solver_entail_wit_4_2_split_goal_4 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp (0 : Int))) ∧ ((Znth q_6 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  ((i + 1) <= (((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) + (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))

noncomputable def solver_entail_wit_4_2_split_goal_5 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp (0 : Int))) ∧ ((Znth q_6 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  ((((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) + (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) <= ((i + 1) * 1000000000))

noncomputable def solver_entail_wit_4_2_split_goal_6 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp (0 : Int))) ∧ ((Znth q_6 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (((-(i + 1)) * 1000000000) <= ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))

noncomputable def solver_entail_wit_4_2_split_goal_7 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp (0 : Int))) ∧ ((Znth q_6 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))

noncomputable def solver_entail_wit_4_2_split_goal_8 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp (0 : Int))) ∧ ((Znth q_6 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= ((i + 1) * 1000000000))

noncomputable def solver_entail_wit_4_2_split_goal_9 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp (0 : Int))) ∧ ((Znth q_6 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  ((i + 1) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))

noncomputable def solver_entail_wit_4_2_split_goal_10 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp (0 : Int))) ∧ ((Znth q_6 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)) <= 1000000000)

noncomputable def solver_entail_wit_4_2_split_goal_11 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp (0 : Int))) ∧ ((Znth q_6 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (1 <= (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))

noncomputable def solver_entail_wit_4_2_split_goal_12 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp (0 : Int))) ∧ ((Znth q_6 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))

noncomputable def solver_entail_wit_4_2_split_goal_13 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) < ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp (0 : Int))) ∧ ((Znth q_6 dp (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))

noncomputable def solver_entail_wit_4_3 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp_2 : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp_2 (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) >= ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp_2 (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 off mind)) ,
  (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp_2)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (intArray.full a_pre n_pre prog)
|--
  (EX dp : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((Znth i prog (0 : Int)) = (Znth i prog (0 : Int))) ” &&
  “ ((Znth (i - 1) prog (0 : Int)) = (Znth (i - 1) prog (0 : Int))) ” &&
  “ (1 <= (Znth i prog (0 : Int))) ” &&
  “ ((Znth i prog (0 : Int)) <= k_pre) ” &&
  “ (1 <= (Znth (i - 1) prog (0 : Int))) ” &&
  “ ((Znth (i - 1) prog (0 : Int)) <= k_pre) ” &&
  “ ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int))) ” &&
  “ ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)) = (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: hot_costs)) ((0 : Int)))) ” &&
  “ (1 <= (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) ” &&
  “ ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)) <= 1000000000) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ (i <= ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) ” &&
  “ (((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) <= (i * 1000000000)) ” &&
  “ ((i + 1) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) ” &&
  “ ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) <= ((i + 1) * 1000000000)) ” &&
  “ (((-i) * 1000000000) <= mind) ” &&
  “ (mind <= (0 : Int)) ” &&
  “ (i <= (mind + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) ” &&
  “ ((mind + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) <= (i * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000))))) ” &&
  “ (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= ((mind + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) + (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: cold_costs)) ((0 : Int))))) ” &&
  “ (((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399) -> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= (((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) + (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: hot_costs)) ((0 : Int)))))) ” &&
  “ (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) = ((mind + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) + (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: cold_costs)) ((0 : Int))))) ” &&
  “ ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) = (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) ” &&
  “ (((-(i + 1)) * 1000000000) <= (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) ” &&
  “ (((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) + (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) <= ((i + 1) * 1000000000)) ” &&
  “ ((i + 1) <= ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) + (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs i dp ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) mind) ” &&
  “ ((((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) < (Znth (Znth (i - 1) prog (0 : Int)) dp (0 : Int))) ∧ ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth ((Znth (i - 1) prog (0 : Int))) ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) (dp)) (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))))) ” &&
  “ ((((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) < (Znth (Znth (i - 1) prog (0 : Int)) dp (0 : Int))) ∧ ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth ((Znth (i - 1) prog (0 : Int))) ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) (dp)) (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) mind)) ” &&
  “ (((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) >= (Znth (Znth (i - 1) prog (0 : Int)) dp (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) mind)) ”
  &&  (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp))
  ||
  (EX dp : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((Znth i prog (0 : Int)) = (Znth i prog (0 : Int))) ” &&
  “ ((Znth (i - 1) prog (0 : Int)) = (Znth (i - 1) prog (0 : Int))) ” &&
  “ (1 <= (Znth i prog (0 : Int))) ” &&
  “ ((Znth i prog (0 : Int)) <= k_pre) ” &&
  “ (1 <= (Znth (i - 1) prog (0 : Int))) ” &&
  “ ((Znth (i - 1) prog (0 : Int)) <= k_pre) ” &&
  “ ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int))) ” &&
  “ ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)) = (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: hot_costs)) ((0 : Int)))) ” &&
  “ (1 <= (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) ” &&
  “ ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)) <= 1000000000) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ (i <= ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) ” &&
  “ (((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) <= (i * 1000000000)) ” &&
  “ ((i + 1) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) ” &&
  “ ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) <= ((i + 1) * 1000000000)) ” &&
  “ (((-i) * 1000000000) <= mind) ” &&
  “ (mind <= (0 : Int)) ” &&
  “ (i <= (mind + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) ” &&
  “ ((mind + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) <= (i * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000))))) ” &&
  “ (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= ((mind + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) + (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: cold_costs)) ((0 : Int))))) ” &&
  “ (((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399) -> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= (((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) + (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: hot_costs)) ((0 : Int)))))) ” &&
  “ ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399) ” &&
  “ (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) = (((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) + (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: hot_costs)) ((0 : Int))))) ” &&
  “ ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) = (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) ” &&
  “ (((-(i + 1)) * 1000000000) <= (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) ” &&
  “ (((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) + (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) <= ((i + 1) * 1000000000)) ” &&
  “ ((i + 1) <= ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) + (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs i dp ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) mind) ” &&
  “ ((((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) < (Znth (Znth (i - 1) prog (0 : Int)) dp (0 : Int))) ∧ ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth ((Znth (i - 1) prog (0 : Int))) ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) (dp)) (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))))) ” &&
  “ ((((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) < (Znth (Znth (i - 1) prog (0 : Int)) dp (0 : Int))) ∧ ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth ((Znth (i - 1) prog (0 : Int))) ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) (dp)) (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) mind)) ” &&
  “ (((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) >= (Znth (Znth (i - 1) prog (0 : Int)) dp (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) mind)) ”
  &&  (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp))

noncomputable def solver_entail_wit_4_4 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp_2 : (List Int)) (i : Int) (PreH1 : ((((Znth (Znth i prog (0 : Int)) dp_2 (0 : Int)) + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) >= ((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (PreH2 : ((Znth (Znth i prog (0 : Int)) dp_2 (0 : Int)) < 4557430888798830399)) (PreH3 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 300000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (prog)))) (PreH10 : (k_pre = (Zlength (cold_costs)))) (PreH11 : (k_pre = (Zlength (hot_costs)))) (PreH12 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH13 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH14 : (1 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH17 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH18 : (i <= off)) (PreH19 : (off <= (i * 1000000000))) (PreH20 : (((-i) * 1000000000) <= mind)) (PreH21 : (mind <= (0 : Int))) (PreH22 : (i <= (mind + off))) (PreH23 : ((mind + off) <= (i * 1000000000))) (PreH24 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH25 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 off mind)) ,
  (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp_2)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (intArray.full a_pre n_pre prog)
|--
  (EX dp : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((Znth i prog (0 : Int)) = (Znth i prog (0 : Int))) ” &&
  “ ((Znth (i - 1) prog (0 : Int)) = (Znth (i - 1) prog (0 : Int))) ” &&
  “ (1 <= (Znth i prog (0 : Int))) ” &&
  “ ((Znth i prog (0 : Int)) <= k_pre) ” &&
  “ (1 <= (Znth (i - 1) prog (0 : Int))) ” &&
  “ ((Znth (i - 1) prog (0 : Int)) <= k_pre) ” &&
  “ ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int))) ” &&
  “ ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)) = (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: cold_costs)) ((0 : Int)))) ” &&
  “ (1 <= (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) ” &&
  “ ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)) <= 1000000000) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ (i <= ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) ” &&
  “ (((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= (i * 1000000000)) ” &&
  “ ((i + 1) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) ” &&
  “ ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= ((i + 1) * 1000000000)) ” &&
  “ (((-i) * 1000000000) <= mind) ” &&
  “ (mind <= (0 : Int)) ” &&
  “ (i <= (mind + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) ” &&
  “ ((mind + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) <= (i * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000))))) ” &&
  “ (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= ((mind + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) + (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: cold_costs)) ((0 : Int))))) ” &&
  “ (((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399) -> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= (((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) + (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: hot_costs)) ((0 : Int)))))) ” &&
  “ (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) = ((mind + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) + (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: cold_costs)) ((0 : Int))))) ” &&
  “ ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) = (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) ” &&
  “ (((-(i + 1)) * 1000000000) <= (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) ” &&
  “ (((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) + (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) <= ((i + 1) * 1000000000)) ” &&
  “ ((i + 1) <= ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) + (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs i dp ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) mind) ” &&
  “ ((((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) < (Znth (Znth (i - 1) prog (0 : Int)) dp (0 : Int))) ∧ ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth ((Znth (i - 1) prog (0 : Int))) ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (dp)) (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))) ” &&
  “ ((((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) < (Znth (Znth (i - 1) prog (0 : Int)) dp (0 : Int))) ∧ ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth ((Znth (i - 1) prog (0 : Int))) ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (dp)) (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) mind)) ” &&
  “ (((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) >= (Znth (Znth (i - 1) prog (0 : Int)) dp (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) mind)) ”
  &&  (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp))
  ||
  (EX dp : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((Znth i prog (0 : Int)) = (Znth i prog (0 : Int))) ” &&
  “ ((Znth (i - 1) prog (0 : Int)) = (Znth (i - 1) prog (0 : Int))) ” &&
  “ (1 <= (Znth i prog (0 : Int))) ” &&
  “ ((Znth i prog (0 : Int)) <= k_pre) ” &&
  “ (1 <= (Znth (i - 1) prog (0 : Int))) ” &&
  “ ((Znth (i - 1) prog (0 : Int)) <= k_pre) ” &&
  “ ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int))) ” &&
  “ ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)) = (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: cold_costs)) ((0 : Int)))) ” &&
  “ (1 <= (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) ” &&
  “ ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)) <= 1000000000) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ (i <= ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) ” &&
  “ (((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= (i * 1000000000)) ” &&
  “ ((i + 1) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) ” &&
  “ ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= ((i + 1) * 1000000000)) ” &&
  “ (((-i) * 1000000000) <= mind) ” &&
  “ (mind <= (0 : Int)) ” &&
  “ (i <= (mind + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) ” &&
  “ ((mind + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) <= (i * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000))))) ” &&
  “ (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= ((mind + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) + (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: cold_costs)) ((0 : Int))))) ” &&
  “ (((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399) -> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= (((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) + (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: hot_costs)) ((0 : Int)))))) ” &&
  “ ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399) ” &&
  “ (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) = (((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) + (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: hot_costs)) ((0 : Int))))) ” &&
  “ ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) = (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) ” &&
  “ (((-(i + 1)) * 1000000000) <= (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) ” &&
  “ (((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) + (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) <= ((i + 1) * 1000000000)) ” &&
  “ ((i + 1) <= ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) + (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs i dp ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) mind) ” &&
  “ ((((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) < (Znth (Znth (i - 1) prog (0 : Int)) dp (0 : Int))) ∧ ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth ((Znth (i - 1) prog (0 : Int))) ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (dp)) (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))) ” &&
  “ ((((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) < (Znth (Znth (i - 1) prog (0 : Int)) dp (0 : Int))) ∧ ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth ((Znth (i - 1) prog (0 : Int))) ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (dp)) (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) mind)) ” &&
  “ (((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) >= (Znth (Znth (i - 1) prog (0 : Int)) dp (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) mind)) ”
  &&  (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp))

noncomputable def solver_entail_wit_4_5 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp_2 : (List Int)) (i : Int) (PreH1 : ((Znth (Znth i prog (0 : Int)) dp_2 (0 : Int)) >= 4557430888798830399)) (PreH2 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH12 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH16 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000))) (PreH19 : (((-i) * 1000000000) <= mind)) (PreH20 : (mind <= (0 : Int))) (PreH21 : (i <= (mind + off))) (PreH22 : ((mind + off) <= (i * 1000000000))) (PreH23 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 off mind)) ,
  (int64Array.full d_pre (k_pre + 1) dp_2)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (intArray.full a_pre n_pre prog)
|--
  (EX dp : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((Znth i prog (0 : Int)) = (Znth i prog (0 : Int))) ” &&
  “ ((Znth (i - 1) prog (0 : Int)) = (Znth (i - 1) prog (0 : Int))) ” &&
  “ (1 <= (Znth i prog (0 : Int))) ” &&
  “ ((Znth i prog (0 : Int)) <= k_pre) ” &&
  “ (1 <= (Znth (i - 1) prog (0 : Int))) ” &&
  “ ((Znth (i - 1) prog (0 : Int)) <= k_pre) ” &&
  “ ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int))) ” &&
  “ ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)) = (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: hot_costs)) ((0 : Int)))) ” &&
  “ (1 <= (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) ” &&
  “ ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)) <= 1000000000) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ (i <= ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) ” &&
  “ (((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) <= (i * 1000000000)) ” &&
  “ ((i + 1) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) ” &&
  “ ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) <= ((i + 1) * 1000000000)) ” &&
  “ (((-i) * 1000000000) <= mind) ” &&
  “ (mind <= (0 : Int)) ” &&
  “ (i <= (mind + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) ” &&
  “ ((mind + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) <= (i * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000))))) ” &&
  “ (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= ((mind + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) + (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: cold_costs)) ((0 : Int))))) ” &&
  “ (((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399) -> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= (((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) + (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: hot_costs)) ((0 : Int)))))) ” &&
  “ (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) = ((mind + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) + (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: cold_costs)) ((0 : Int))))) ” &&
  “ ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) = (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) ” &&
  “ (((-(i + 1)) * 1000000000) <= (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) ” &&
  “ (((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) + (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) <= ((i + 1) * 1000000000)) ” &&
  “ ((i + 1) <= ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) + (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs i dp ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) mind) ” &&
  “ ((((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) < (Znth (Znth (i - 1) prog (0 : Int)) dp (0 : Int))) ∧ ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth ((Znth (i - 1) prog (0 : Int))) ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) (dp)) (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))))) ” &&
  “ ((((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) < (Znth (Znth (i - 1) prog (0 : Int)) dp (0 : Int))) ∧ ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth ((Znth (i - 1) prog (0 : Int))) ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) (dp)) (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) mind)) ” &&
  “ (((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) >= (Znth (Znth (i - 1) prog (0 : Int)) dp (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) mind)) ”
  &&  (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp))
  ||
  (EX dp : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((Znth i prog (0 : Int)) = (Znth i prog (0 : Int))) ” &&
  “ ((Znth (i - 1) prog (0 : Int)) = (Znth (i - 1) prog (0 : Int))) ” &&
  “ (1 <= (Znth i prog (0 : Int))) ” &&
  “ ((Znth i prog (0 : Int)) <= k_pre) ” &&
  “ (1 <= (Znth (i - 1) prog (0 : Int))) ” &&
  “ ((Znth (i - 1) prog (0 : Int)) <= k_pre) ” &&
  “ ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int))) ” &&
  “ ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)) = (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: hot_costs)) ((0 : Int)))) ” &&
  “ (1 <= (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) ” &&
  “ ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)) <= 1000000000) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ (i <= ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) ” &&
  “ (((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) <= (i * 1000000000)) ” &&
  “ ((i + 1) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) ” &&
  “ ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) <= ((i + 1) * 1000000000)) ” &&
  “ (((-i) * 1000000000) <= mind) ” &&
  “ (mind <= (0 : Int)) ” &&
  “ (i <= (mind + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) ” &&
  “ ((mind + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) <= (i * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000))))) ” &&
  “ (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= ((mind + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) + (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: cold_costs)) ((0 : Int))))) ” &&
  “ (((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399) -> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= (((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) + (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: hot_costs)) ((0 : Int)))))) ” &&
  “ ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399) ” &&
  “ (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) = (((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) + (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: hot_costs)) ((0 : Int))))) ” &&
  “ ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) = (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) ” &&
  “ (((-(i + 1)) * 1000000000) <= (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) ” &&
  “ (((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) + (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) <= ((i + 1) * 1000000000)) ” &&
  “ ((i + 1) <= ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) + (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs i dp ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) mind) ” &&
  “ ((((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) < (Znth (Znth (i - 1) prog (0 : Int)) dp (0 : Int))) ∧ ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth ((Znth (i - 1) prog (0 : Int))) ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) (dp)) (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))))) ” &&
  “ ((((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) < (Znth (Znth (i - 1) prog (0 : Int)) dp (0 : Int))) ∧ ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth ((Znth (i - 1) prog (0 : Int))) ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))) (dp)) (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) mind)) ” &&
  “ (((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int)))) >= (Znth (Znth (i - 1) prog (0 : Int)) dp (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))) mind)) ”
  &&  (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp))

noncomputable def solver_entail_wit_4_6 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp_2 : (List Int)) (i : Int) (PreH1 : ((Znth (Znth i prog (0 : Int)) dp_2 (0 : Int)) >= 4557430888798830399)) (PreH2 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH12 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH16 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000))) (PreH19 : (((-i) * 1000000000) <= mind)) (PreH20 : (mind <= (0 : Int))) (PreH21 : (i <= (mind + off))) (PreH22 : ((mind + off) <= (i * 1000000000))) (PreH23 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 off mind)) ,
  (int64Array.full d_pre (k_pre + 1) dp_2)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  (EX dp : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((Znth i prog (0 : Int)) = (Znth i prog (0 : Int))) ” &&
  “ ((Znth (i - 1) prog (0 : Int)) = (Znth (i - 1) prog (0 : Int))) ” &&
  “ (1 <= (Znth i prog (0 : Int))) ” &&
  “ ((Znth i prog (0 : Int)) <= k_pre) ” &&
  “ (1 <= (Znth (i - 1) prog (0 : Int))) ” &&
  “ ((Znth (i - 1) prog (0 : Int)) <= k_pre) ” &&
  “ ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int))) ” &&
  “ ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)) = (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: cold_costs)) ((0 : Int)))) ” &&
  “ (1 <= (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) ” &&
  “ ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)) <= 1000000000) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ (i <= ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) ” &&
  “ (((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= (i * 1000000000)) ” &&
  “ ((i + 1) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) ” &&
  “ ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= ((i + 1) * 1000000000)) ” &&
  “ (((-i) * 1000000000) <= mind) ” &&
  “ (mind <= (0 : Int)) ” &&
  “ (i <= (mind + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) ” &&
  “ ((mind + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) <= (i * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000))))) ” &&
  “ (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= ((mind + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) + (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: cold_costs)) ((0 : Int))))) ” &&
  “ (((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399) -> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= (((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) + (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: hot_costs)) ((0 : Int)))))) ” &&
  “ (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) = ((mind + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) + (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: cold_costs)) ((0 : Int))))) ” &&
  “ ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) = (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) ” &&
  “ (((-(i + 1)) * 1000000000) <= (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) ” &&
  “ (((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) + (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) <= ((i + 1) * 1000000000)) ” &&
  “ ((i + 1) <= ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) + (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs i dp ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) mind) ” &&
  “ ((((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) < (Znth (Znth (i - 1) prog (0 : Int)) dp (0 : Int))) ∧ ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth ((Znth (i - 1) prog (0 : Int))) ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (dp)) (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))) ” &&
  “ ((((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) < (Znth (Znth (i - 1) prog (0 : Int)) dp (0 : Int))) ∧ ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth ((Znth (i - 1) prog (0 : Int))) ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (dp)) (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) mind)) ” &&
  “ (((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) >= (Znth (Znth (i - 1) prog (0 : Int)) dp (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) mind)) ”
  &&  (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp))
  ||
  (EX dp : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((Znth i prog (0 : Int)) = (Znth i prog (0 : Int))) ” &&
  “ ((Znth (i - 1) prog (0 : Int)) = (Znth (i - 1) prog (0 : Int))) ” &&
  “ (1 <= (Znth i prog (0 : Int))) ” &&
  “ ((Znth i prog (0 : Int)) <= k_pre) ” &&
  “ (1 <= (Znth (i - 1) prog (0 : Int))) ” &&
  “ ((Znth (i - 1) prog (0 : Int)) <= k_pre) ” &&
  “ ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int))) ” &&
  “ ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)) = (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: cold_costs)) ((0 : Int)))) ” &&
  “ (1 <= (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) ” &&
  “ ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)) <= 1000000000) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ (i <= ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) ” &&
  “ (((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= (i * 1000000000)) ” &&
  “ ((i + 1) <= (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) ” &&
  “ ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= ((i + 1) * 1000000000)) ” &&
  “ (((-i) * 1000000000) <= mind) ” &&
  “ (mind <= (0 : Int)) ” &&
  “ (i <= (mind + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) ” &&
  “ ((mind + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) <= (i * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000))))) ” &&
  “ (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= ((mind + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) + (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: cold_costs)) ((0 : Int))))) ” &&
  “ (((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399) -> (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) <= (((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) + (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: hot_costs)) ((0 : Int)))))) ” &&
  “ ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399) ” &&
  “ (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) = (((Znth (Znth i prog (0 : Int)) dp (0 : Int)) + ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) + (Znth ((Znth i prog (0 : Int))) (((0 : Int) :: hot_costs)) ((0 : Int))))) ” &&
  “ ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) = (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) ” &&
  “ (((-(i + 1)) * 1000000000) <= (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) ” &&
  “ (((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) + (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) <= ((i + 1) * 1000000000)) ” &&
  “ ((i + 1) <= ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) + (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs i dp ((off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) mind) ” &&
  “ ((((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) < (Znth (Znth (i - 1) prog (0 : Int)) dp (0 : Int))) ∧ ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth ((Znth (i - 1) prog (0 : Int))) ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (dp)) (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) (((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))))) ” &&
  “ ((((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) < (Znth (Znth (i - 1) prog (0 : Int)) dp (0 : Int))) ∧ ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth ((Znth (i - 1) prog (0 : Int))) ((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))) (dp)) (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) mind)) ” &&
  “ (((((mind + off) + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) - (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int)))) >= (Znth (Znth (i - 1) prog (0 : Int)) dp (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp (off + (Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))) mind)) ”
  &&  (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp))

noncomputable def solver_entail_wit_5_1 : Prop :=
  (
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny < mind)) (PreH2 : (ny < (Znth y dp_2 (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x = y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH45 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  (int64Array.full d_pre (k_pre + 1) (replace_Znth (y) (ny) (dp_2)))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  EX dp : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ ((i + 1) <= off) ” &&
  “ (off <= ((i + 1) * 1000000000)) ” &&
  “ (((-(i + 1)) * 1000000000) <= ny) ” &&
  “ (ny <= (0 : Int)) ” &&
  “ ((i + 1) <= (ny + off)) ” &&
  “ ((ny + off) <= ((i + 1) * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-(i + 1)) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= ((i + 1) * 1000000000))))) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp off ny) ”
  &&  (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
) \/
(
forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny < mind)) (PreH2 : (ny < (Znth y dp_2 (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x = y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH45 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  TT && emp 
|--
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 (replace_Znth (y) (ny) (dp_2)) (0 : Int)) = 4557430888798830399) ∨ ((((-(i + 1)) * 1000000000) <= (Znth q_3 (replace_Znth (y) (ny) (dp_2)) (0 : Int))) ∧ ((Znth q_3 (replace_Znth (y) (ny) (dp_2)) (0 : Int)) <= ((i + 1) * 1000000000))))) ” &&
  “ ((Znth (0 : Int) (replace_Znth (x) ((candB - off)) (dp_2)) (0 : Int)) = (0 : Int)) ” &&
  “ ((Zlength ((replace_Znth (x) ((candB - off)) (dp_2)))) = (k_pre + 1)) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ”
  &&  emp
)

noncomputable def solver_entail_wit_5_1_split_goal_1 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny < mind)) (PreH2 : (ny < (Znth y dp_2 (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x = y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH45 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 (replace_Znth (y) (ny) (dp_2)) (0 : Int)) = 4557430888798830399) ∨ ((((-(i + 1)) * 1000000000) <= (Znth q_3 (replace_Znth (y) (ny) (dp_2)) (0 : Int))) ∧ ((Znth q_3 (replace_Znth (y) (ny) (dp_2)) (0 : Int)) <= ((i + 1) * 1000000000)))))

noncomputable def solver_entail_wit_5_1_split_goal_2 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny < mind)) (PreH2 : (ny < (Znth y dp_2 (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x = y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH45 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  ((Znth (0 : Int) (replace_Znth (x) ((candB - off)) (dp_2)) (0 : Int)) = (0 : Int))

noncomputable def solver_entail_wit_5_1_split_goal_3 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny < mind)) (PreH2 : (ny < (Znth y dp_2 (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x = y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH45 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  ((Zlength ((replace_Znth (x) ((candB - off)) (dp_2)))) = (k_pre + 1))

noncomputable def solver_entail_wit_5_1_split_goal_4 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny < mind)) (PreH2 : (ny < (Znth y dp_2 (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x = y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH45 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))

noncomputable def solver_entail_wit_5_1_split_goal_5 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny < mind)) (PreH2 : (ny < (Znth y dp_2 (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x = y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH45 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))

noncomputable def solver_entail_wit_5_2 : Prop :=
  (
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny < mind)) (PreH2 : (ny < (Znth y dp_2 (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x ≠ y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : ((Znth x dp_2 (0 : Int)) < 4557430888798830399)) (PreH38 : (candB = (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) (PreH39 : (ny = (candB - off))) (PreH40 : (((-(i + 1)) * 1000000000) <= ny)) (PreH41 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH42 : ((i + 1) <= (ny + off))) (PreH43 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH45 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH46 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  (int64Array.full d_pre (k_pre + 1) (replace_Znth (y) (ny) (dp_2)))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  EX dp : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ ((i + 1) <= off) ” &&
  “ (off <= ((i + 1) * 1000000000)) ” &&
  “ (((-(i + 1)) * 1000000000) <= ny) ” &&
  “ (ny <= (0 : Int)) ” &&
  “ ((i + 1) <= (ny + off)) ” &&
  “ ((ny + off) <= ((i + 1) * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-(i + 1)) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= ((i + 1) * 1000000000))))) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp off ny) ”
  &&  (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
) \/
(
forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny < mind)) (PreH2 : (ny < (Znth y dp_2 (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x ≠ y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : ((Znth x dp_2 (0 : Int)) < 4557430888798830399)) (PreH38 : (candB = (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) (PreH39 : (ny = (candB - off))) (PreH40 : (((-(i + 1)) * 1000000000) <= ny)) (PreH41 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH42 : ((i + 1) <= (ny + off))) (PreH43 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH45 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH46 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  TT && emp 
|--
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 (replace_Znth (y) (ny) (dp_2)) (0 : Int)) = 4557430888798830399) ∨ ((((-(i + 1)) * 1000000000) <= (Znth q_3 (replace_Znth (y) (ny) (dp_2)) (0 : Int))) ∧ ((Znth q_3 (replace_Znth (y) (ny) (dp_2)) (0 : Int)) <= ((i + 1) * 1000000000))))) ” &&
  “ ((Znth (0 : Int) (replace_Znth (y) ((candB - off)) (dp_2)) (0 : Int)) = (0 : Int)) ” &&
  “ ((Zlength ((replace_Znth (y) ((candB - off)) (dp_2)))) = (k_pre + 1)) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ”
  &&  emp
)

noncomputable def solver_entail_wit_5_2_split_goal_1 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny < mind)) (PreH2 : (ny < (Znth y dp_2 (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x ≠ y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : ((Znth x dp_2 (0 : Int)) < 4557430888798830399)) (PreH38 : (candB = (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) (PreH39 : (ny = (candB - off))) (PreH40 : (((-(i + 1)) * 1000000000) <= ny)) (PreH41 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH42 : ((i + 1) <= (ny + off))) (PreH43 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH45 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH46 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 (replace_Znth (y) (ny) (dp_2)) (0 : Int)) = 4557430888798830399) ∨ ((((-(i + 1)) * 1000000000) <= (Znth q_3 (replace_Znth (y) (ny) (dp_2)) (0 : Int))) ∧ ((Znth q_3 (replace_Znth (y) (ny) (dp_2)) (0 : Int)) <= ((i + 1) * 1000000000)))))

noncomputable def solver_entail_wit_5_2_split_goal_2 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny < mind)) (PreH2 : (ny < (Znth y dp_2 (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x ≠ y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : ((Znth x dp_2 (0 : Int)) < 4557430888798830399)) (PreH38 : (candB = (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) (PreH39 : (ny = (candB - off))) (PreH40 : (((-(i + 1)) * 1000000000) <= ny)) (PreH41 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH42 : ((i + 1) <= (ny + off))) (PreH43 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH45 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH46 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  ((Znth (0 : Int) (replace_Znth (y) ((candB - off)) (dp_2)) (0 : Int)) = (0 : Int))

noncomputable def solver_entail_wit_5_2_split_goal_3 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny < mind)) (PreH2 : (ny < (Znth y dp_2 (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x ≠ y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : ((Znth x dp_2 (0 : Int)) < 4557430888798830399)) (PreH38 : (candB = (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) (PreH39 : (ny = (candB - off))) (PreH40 : (((-(i + 1)) * 1000000000) <= ny)) (PreH41 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH42 : ((i + 1) <= (ny + off))) (PreH43 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH45 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH46 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  ((Zlength ((replace_Znth (y) ((candB - off)) (dp_2)))) = (k_pre + 1))

noncomputable def solver_entail_wit_5_2_split_goal_4 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny < mind)) (PreH2 : (ny < (Znth y dp_2 (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x ≠ y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : ((Znth x dp_2 (0 : Int)) < 4557430888798830399)) (PreH38 : (candB = (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) (PreH39 : (ny = (candB - off))) (PreH40 : (((-(i + 1)) * 1000000000) <= ny)) (PreH41 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH42 : ((i + 1) <= (ny + off))) (PreH43 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH45 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH46 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))

noncomputable def solver_entail_wit_5_2_split_goal_5 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny < mind)) (PreH2 : (ny < (Znth y dp_2 (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x ≠ y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : ((Znth x dp_2 (0 : Int)) < 4557430888798830399)) (PreH38 : (candB = (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) (PreH39 : (ny = (candB - off))) (PreH40 : (((-(i + 1)) * 1000000000) <= ny)) (PreH41 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH42 : ((i + 1) <= (ny + off))) (PreH43 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH45 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH46 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))

noncomputable def solver_entail_wit_5_3 : Prop :=
  (
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x = y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH45 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  (int64Array.full d_pre (k_pre + 1) (replace_Znth (y) (ny) (dp_2)))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  EX dp : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ ((i + 1) <= off) ” &&
  “ (off <= ((i + 1) * 1000000000)) ” &&
  “ (((-(i + 1)) * 1000000000) <= mind) ” &&
  “ (mind <= (0 : Int)) ” &&
  “ ((i + 1) <= (mind + off)) ” &&
  “ ((mind + off) <= ((i + 1) * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-(i + 1)) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= ((i + 1) * 1000000000))))) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp off mind) ”
  &&  (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
) \/
(
forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x = y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH45 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  TT && emp 
|--
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 (replace_Znth (y) (ny) (dp_2)) (0 : Int)) = 4557430888798830399) ∨ ((((-(i + 1)) * 1000000000) <= (Znth q_3 (replace_Znth (y) (ny) (dp_2)) (0 : Int))) ∧ ((Znth q_3 (replace_Znth (y) (ny) (dp_2)) (0 : Int)) <= ((i + 1) * 1000000000))))) ” &&
  “ ((Znth (0 : Int) (replace_Znth (x) ((candB - off)) (dp_2)) (0 : Int)) = (0 : Int)) ” &&
  “ ((Zlength ((replace_Znth (x) ((candB - off)) (dp_2)))) = (k_pre + 1)) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ”
  &&  emp
)

noncomputable def solver_entail_wit_5_3_split_goal_1 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x = y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH45 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 (replace_Znth (y) (ny) (dp_2)) (0 : Int)) = 4557430888798830399) ∨ ((((-(i + 1)) * 1000000000) <= (Znth q_3 (replace_Znth (y) (ny) (dp_2)) (0 : Int))) ∧ ((Znth q_3 (replace_Znth (y) (ny) (dp_2)) (0 : Int)) <= ((i + 1) * 1000000000)))))

noncomputable def solver_entail_wit_5_3_split_goal_2 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x = y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH45 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  ((Znth (0 : Int) (replace_Znth (x) ((candB - off)) (dp_2)) (0 : Int)) = (0 : Int))

noncomputable def solver_entail_wit_5_3_split_goal_3 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x = y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH45 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  ((Zlength ((replace_Znth (x) ((candB - off)) (dp_2)))) = (k_pre + 1))

noncomputable def solver_entail_wit_5_3_split_goal_4 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x = y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH45 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))

noncomputable def solver_entail_wit_5_3_split_goal_5 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x = y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH45 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))

noncomputable def solver_entail_wit_5_4 : Prop :=
  (
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x ≠ y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH45 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  (int64Array.full d_pre (k_pre + 1) (replace_Znth (y) (ny) (dp_2)))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  EX dp : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ ((i + 1) <= off) ” &&
  “ (off <= ((i + 1) * 1000000000)) ” &&
  “ (((-(i + 1)) * 1000000000) <= mind) ” &&
  “ (mind <= (0 : Int)) ” &&
  “ ((i + 1) <= (mind + off)) ” &&
  “ ((mind + off) <= ((i + 1) * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-(i + 1)) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= ((i + 1) * 1000000000))))) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp off mind) ”
  &&  (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
) \/
(
forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x ≠ y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH45 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  TT && emp 
|--
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 (replace_Znth (y) (ny) (dp_2)) (0 : Int)) = 4557430888798830399) ∨ ((((-(i + 1)) * 1000000000) <= (Znth q_3 (replace_Znth (y) (ny) (dp_2)) (0 : Int))) ∧ ((Znth q_3 (replace_Znth (y) (ny) (dp_2)) (0 : Int)) <= ((i + 1) * 1000000000))))) ” &&
  “ ((Znth (0 : Int) (replace_Znth (y) ((candB - off)) (dp_2)) (0 : Int)) = (0 : Int)) ” &&
  “ ((Zlength ((replace_Znth (y) ((candB - off)) (dp_2)))) = (k_pre + 1)) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ”
  &&  emp
)

noncomputable def solver_entail_wit_5_4_split_goal_1 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x ≠ y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH45 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 (replace_Znth (y) (ny) (dp_2)) (0 : Int)) = 4557430888798830399) ∨ ((((-(i + 1)) * 1000000000) <= (Znth q_3 (replace_Znth (y) (ny) (dp_2)) (0 : Int))) ∧ ((Znth q_3 (replace_Znth (y) (ny) (dp_2)) (0 : Int)) <= ((i + 1) * 1000000000)))))

noncomputable def solver_entail_wit_5_4_split_goal_2 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x ≠ y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH45 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  ((Znth (0 : Int) (replace_Znth (y) ((candB - off)) (dp_2)) (0 : Int)) = (0 : Int))

noncomputable def solver_entail_wit_5_4_split_goal_3 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x ≠ y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH45 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  ((Zlength ((replace_Znth (y) ((candB - off)) (dp_2)))) = (k_pre + 1))

noncomputable def solver_entail_wit_5_4_split_goal_4 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x ≠ y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH45 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))

noncomputable def solver_entail_wit_5_4_split_goal_5 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x ≠ y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH45 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))

noncomputable def solver_entail_wit_5_5 : Prop :=
  (
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x ≠ y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : ((Znth x dp_2 (0 : Int)) < 4557430888798830399)) (PreH38 : (candB = (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) (PreH39 : (ny = (candB - off))) (PreH40 : (((-(i + 1)) * 1000000000) <= ny)) (PreH41 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH42 : ((i + 1) <= (ny + off))) (PreH43 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH45 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH46 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  (int64Array.full d_pre (k_pre + 1) (replace_Znth (y) (ny) (dp_2)))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  EX dp : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ ((i + 1) <= off) ” &&
  “ (off <= ((i + 1) * 1000000000)) ” &&
  “ (((-(i + 1)) * 1000000000) <= mind) ” &&
  “ (mind <= (0 : Int)) ” &&
  “ ((i + 1) <= (mind + off)) ” &&
  “ ((mind + off) <= ((i + 1) * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-(i + 1)) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= ((i + 1) * 1000000000))))) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp off mind) ”
  &&  (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
) \/
(
forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x ≠ y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : ((Znth x dp_2 (0 : Int)) < 4557430888798830399)) (PreH38 : (candB = (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) (PreH39 : (ny = (candB - off))) (PreH40 : (((-(i + 1)) * 1000000000) <= ny)) (PreH41 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH42 : ((i + 1) <= (ny + off))) (PreH43 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH45 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH46 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  TT && emp 
|--
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 (replace_Znth (y) (ny) (dp_2)) (0 : Int)) = 4557430888798830399) ∨ ((((-(i + 1)) * 1000000000) <= (Znth q_3 (replace_Znth (y) (ny) (dp_2)) (0 : Int))) ∧ ((Znth q_3 (replace_Znth (y) (ny) (dp_2)) (0 : Int)) <= ((i + 1) * 1000000000))))) ” &&
  “ ((Znth (0 : Int) (replace_Znth (y) ((candB - off)) (dp_2)) (0 : Int)) = (0 : Int)) ” &&
  “ ((Zlength ((replace_Znth (y) ((candB - off)) (dp_2)))) = (k_pre + 1)) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ”
  &&  emp
)

noncomputable def solver_entail_wit_5_5_split_goal_1 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x ≠ y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : ((Znth x dp_2 (0 : Int)) < 4557430888798830399)) (PreH38 : (candB = (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) (PreH39 : (ny = (candB - off))) (PreH40 : (((-(i + 1)) * 1000000000) <= ny)) (PreH41 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH42 : ((i + 1) <= (ny + off))) (PreH43 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH45 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH46 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 (replace_Znth (y) (ny) (dp_2)) (0 : Int)) = 4557430888798830399) ∨ ((((-(i + 1)) * 1000000000) <= (Znth q_3 (replace_Znth (y) (ny) (dp_2)) (0 : Int))) ∧ ((Znth q_3 (replace_Znth (y) (ny) (dp_2)) (0 : Int)) <= ((i + 1) * 1000000000)))))

noncomputable def solver_entail_wit_5_5_split_goal_2 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x ≠ y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : ((Znth x dp_2 (0 : Int)) < 4557430888798830399)) (PreH38 : (candB = (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) (PreH39 : (ny = (candB - off))) (PreH40 : (((-(i + 1)) * 1000000000) <= ny)) (PreH41 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH42 : ((i + 1) <= (ny + off))) (PreH43 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH45 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH46 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  ((Znth (0 : Int) (replace_Znth (y) ((candB - off)) (dp_2)) (0 : Int)) = (0 : Int))

noncomputable def solver_entail_wit_5_5_split_goal_3 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x ≠ y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : ((Znth x dp_2 (0 : Int)) < 4557430888798830399)) (PreH38 : (candB = (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) (PreH39 : (ny = (candB - off))) (PreH40 : (((-(i + 1)) * 1000000000) <= ny)) (PreH41 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH42 : ((i + 1) <= (ny + off))) (PreH43 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH45 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH46 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  ((Zlength ((replace_Znth (y) ((candB - off)) (dp_2)))) = (k_pre + 1))

noncomputable def solver_entail_wit_5_5_split_goal_4 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x ≠ y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : ((Znth x dp_2 (0 : Int)) < 4557430888798830399)) (PreH38 : (candB = (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) (PreH39 : (ny = (candB - off))) (PreH40 : (((-(i + 1)) * 1000000000) <= ny)) (PreH41 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH42 : ((i + 1) <= (ny + off))) (PreH43 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH45 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH46 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))

noncomputable def solver_entail_wit_5_5_split_goal_5 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= mind)) (PreH2 : (ny < (Znth y dp_2 (0 : Int)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (x = (Znth i prog (0 : Int)))) (PreH15 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH16 : (1 <= x)) (PreH17 : (x <= k_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= k_pre)) (PreH20 : (x ≠ y)) (PreH21 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH22 : (1 <= costA)) (PreH23 : (costA <= 1000000000)) (PreH24 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH25 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH26 : (i <= (off - costA))) (PreH27 : ((off - costA) <= (i * 1000000000))) (PreH28 : ((i + 1) <= off)) (PreH29 : (off <= ((i + 1) * 1000000000))) (PreH30 : (((-i) * 1000000000) <= mind)) (PreH31 : (mind <= (0 : Int))) (PreH32 : (i <= (mind + (off - costA)))) (PreH33 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH34 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH35 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH37 : ((Znth x dp_2 (0 : Int)) < 4557430888798830399)) (PreH38 : (candB = (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) (PreH39 : (ny = (candB - off))) (PreH40 : (((-(i + 1)) * 1000000000) <= ny)) (PreH41 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH42 : ((i + 1) <= (ny + off))) (PreH43 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH45 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH46 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))

noncomputable def solver_entail_wit_5_6 : Prop :=
  (
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= (Znth y dp_2 (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog (0 : Int)))) (PreH14 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x = y)) (PreH20 : (costA = (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH24 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH25 : (i <= (off - costA))) (PreH26 : ((off - costA) <= (i * 1000000000))) (PreH27 : ((i + 1) <= off)) (PreH28 : (off <= ((i + 1) * 1000000000))) (PreH29 : (((-i) * 1000000000) <= mind)) (PreH30 : (mind <= (0 : Int))) (PreH31 : (i <= (mind + (off - costA)))) (PreH32 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH33 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH34 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH35 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH36 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH37 : (ny = (candB - off))) (PreH38 : (((-(i + 1)) * 1000000000) <= ny)) (PreH39 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH40 : ((i + 1) <= (ny + off))) (PreH41 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH42 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH44 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  (int64Array.full d_pre (k_pre + 1) dp_2)
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  EX dp : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ ((i + 1) <= off) ” &&
  “ (off <= ((i + 1) * 1000000000)) ” &&
  “ (((-(i + 1)) * 1000000000) <= mind) ” &&
  “ (mind <= (0 : Int)) ” &&
  “ ((i + 1) <= (mind + off)) ” &&
  “ ((mind + off) <= ((i + 1) * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-(i + 1)) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= ((i + 1) * 1000000000))))) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp off mind) ”
  &&  (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
) \/
(
forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= (Znth y dp_2 (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog (0 : Int)))) (PreH14 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x = y)) (PreH20 : (costA = (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH24 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH25 : (i <= (off - costA))) (PreH26 : ((off - costA) <= (i * 1000000000))) (PreH27 : ((i + 1) <= off)) (PreH28 : (off <= ((i + 1) * 1000000000))) (PreH29 : (((-i) * 1000000000) <= mind)) (PreH30 : (mind <= (0 : Int))) (PreH31 : (i <= (mind + (off - costA)))) (PreH32 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH33 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH34 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH35 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH36 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH37 : (ny = (candB - off))) (PreH38 : (((-(i + 1)) * 1000000000) <= ny)) (PreH39 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH40 : ((i + 1) <= (ny + off))) (PreH41 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH42 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH44 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  TT && emp 
|--
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-(i + 1)) * 1000000000) <= (Znth q_3 dp_2 (0 : Int))) ∧ ((Znth q_3 dp_2 (0 : Int)) <= ((i + 1) * 1000000000))))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ”
  &&  emp
)

noncomputable def solver_entail_wit_5_6_split_goal_1 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= (Znth y dp_2 (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog (0 : Int)))) (PreH14 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x = y)) (PreH20 : (costA = (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH24 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH25 : (i <= (off - costA))) (PreH26 : ((off - costA) <= (i * 1000000000))) (PreH27 : ((i + 1) <= off)) (PreH28 : (off <= ((i + 1) * 1000000000))) (PreH29 : (((-i) * 1000000000) <= mind)) (PreH30 : (mind <= (0 : Int))) (PreH31 : (i <= (mind + (off - costA)))) (PreH32 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH33 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH34 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH35 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH36 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH37 : (ny = (candB - off))) (PreH38 : (((-(i + 1)) * 1000000000) <= ny)) (PreH39 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH40 : ((i + 1) <= (ny + off))) (PreH41 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH42 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH44 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-(i + 1)) * 1000000000) <= (Znth q_3 dp_2 (0 : Int))) ∧ ((Znth q_3 dp_2 (0 : Int)) <= ((i + 1) * 1000000000)))))

noncomputable def solver_entail_wit_5_6_split_goal_2 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= (Znth y dp_2 (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog (0 : Int)))) (PreH14 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x = y)) (PreH20 : (costA = (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH24 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH25 : (i <= (off - costA))) (PreH26 : ((off - costA) <= (i * 1000000000))) (PreH27 : ((i + 1) <= off)) (PreH28 : (off <= ((i + 1) * 1000000000))) (PreH29 : (((-i) * 1000000000) <= mind)) (PreH30 : (mind <= (0 : Int))) (PreH31 : (i <= (mind + (off - costA)))) (PreH32 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH33 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH34 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH35 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH36 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH37 : (ny = (candB - off))) (PreH38 : (((-(i + 1)) * 1000000000) <= ny)) (PreH39 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH40 : ((i + 1) <= (ny + off))) (PreH41 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH42 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH44 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))

noncomputable def solver_entail_wit_5_6_split_goal_3 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= (Znth y dp_2 (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog (0 : Int)))) (PreH14 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x = y)) (PreH20 : (costA = (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH24 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH25 : (i <= (off - costA))) (PreH26 : ((off - costA) <= (i * 1000000000))) (PreH27 : ((i + 1) <= off)) (PreH28 : (off <= ((i + 1) * 1000000000))) (PreH29 : (((-i) * 1000000000) <= mind)) (PreH30 : (mind <= (0 : Int))) (PreH31 : (i <= (mind + (off - costA)))) (PreH32 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH33 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH34 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH35 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH36 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH37 : (ny = (candB - off))) (PreH38 : (((-(i + 1)) * 1000000000) <= ny)) (PreH39 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH40 : ((i + 1) <= (ny + off))) (PreH41 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH42 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH44 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))

noncomputable def solver_entail_wit_5_7 : Prop :=
  (
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= (Znth y dp_2 (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog (0 : Int)))) (PreH14 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x = y)) (PreH20 : (costA = (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH24 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH25 : (i <= (off - costA))) (PreH26 : ((off - costA) <= (i * 1000000000))) (PreH27 : ((i + 1) <= off)) (PreH28 : (off <= ((i + 1) * 1000000000))) (PreH29 : (((-i) * 1000000000) <= mind)) (PreH30 : (mind <= (0 : Int))) (PreH31 : (i <= (mind + (off - costA)))) (PreH32 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH33 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH34 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH35 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH36 : ((Znth x dp_2 (0 : Int)) < 4557430888798830399)) (PreH37 : (candB = (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH45 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  (int64Array.full d_pre (k_pre + 1) dp_2)
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  EX dp : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ ((i + 1) <= off) ” &&
  “ (off <= ((i + 1) * 1000000000)) ” &&
  “ (((-(i + 1)) * 1000000000) <= mind) ” &&
  “ (mind <= (0 : Int)) ” &&
  “ ((i + 1) <= (mind + off)) ” &&
  “ ((mind + off) <= ((i + 1) * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-(i + 1)) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= ((i + 1) * 1000000000))))) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp off mind) ”
  &&  (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
) \/
(
forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= (Znth y dp_2 (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog (0 : Int)))) (PreH14 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x = y)) (PreH20 : (costA = (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH24 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH25 : (i <= (off - costA))) (PreH26 : ((off - costA) <= (i * 1000000000))) (PreH27 : ((i + 1) <= off)) (PreH28 : (off <= ((i + 1) * 1000000000))) (PreH29 : (((-i) * 1000000000) <= mind)) (PreH30 : (mind <= (0 : Int))) (PreH31 : (i <= (mind + (off - costA)))) (PreH32 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH33 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH34 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH35 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH36 : ((Znth x dp_2 (0 : Int)) < 4557430888798830399)) (PreH37 : (candB = (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH45 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  TT && emp 
|--
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-(i + 1)) * 1000000000) <= (Znth q_3 dp_2 (0 : Int))) ∧ ((Znth q_3 dp_2 (0 : Int)) <= ((i + 1) * 1000000000))))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ”
  &&  emp
)

noncomputable def solver_entail_wit_5_7_split_goal_1 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= (Znth y dp_2 (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog (0 : Int)))) (PreH14 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x = y)) (PreH20 : (costA = (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH24 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH25 : (i <= (off - costA))) (PreH26 : ((off - costA) <= (i * 1000000000))) (PreH27 : ((i + 1) <= off)) (PreH28 : (off <= ((i + 1) * 1000000000))) (PreH29 : (((-i) * 1000000000) <= mind)) (PreH30 : (mind <= (0 : Int))) (PreH31 : (i <= (mind + (off - costA)))) (PreH32 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH33 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH34 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH35 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH36 : ((Znth x dp_2 (0 : Int)) < 4557430888798830399)) (PreH37 : (candB = (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH45 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-(i + 1)) * 1000000000) <= (Znth q_3 dp_2 (0 : Int))) ∧ ((Znth q_3 dp_2 (0 : Int)) <= ((i + 1) * 1000000000)))))

noncomputable def solver_entail_wit_5_7_split_goal_2 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= (Znth y dp_2 (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog (0 : Int)))) (PreH14 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x = y)) (PreH20 : (costA = (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH24 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH25 : (i <= (off - costA))) (PreH26 : ((off - costA) <= (i * 1000000000))) (PreH27 : ((i + 1) <= off)) (PreH28 : (off <= ((i + 1) * 1000000000))) (PreH29 : (((-i) * 1000000000) <= mind)) (PreH30 : (mind <= (0 : Int))) (PreH31 : (i <= (mind + (off - costA)))) (PreH32 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH33 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH34 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH35 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH36 : ((Znth x dp_2 (0 : Int)) < 4557430888798830399)) (PreH37 : (candB = (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH45 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))

noncomputable def solver_entail_wit_5_7_split_goal_3 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= (Znth y dp_2 (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog (0 : Int)))) (PreH14 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x = y)) (PreH20 : (costA = (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH24 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH25 : (i <= (off - costA))) (PreH26 : ((off - costA) <= (i * 1000000000))) (PreH27 : ((i + 1) <= off)) (PreH28 : (off <= ((i + 1) * 1000000000))) (PreH29 : (((-i) * 1000000000) <= mind)) (PreH30 : (mind <= (0 : Int))) (PreH31 : (i <= (mind + (off - costA)))) (PreH32 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH33 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH34 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH35 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH36 : ((Znth x dp_2 (0 : Int)) < 4557430888798830399)) (PreH37 : (candB = (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH45 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))

noncomputable def solver_entail_wit_5_8 : Prop :=
  (
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= (Znth y dp_2 (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog (0 : Int)))) (PreH14 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x ≠ y)) (PreH20 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH24 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH25 : (i <= (off - costA))) (PreH26 : ((off - costA) <= (i * 1000000000))) (PreH27 : ((i + 1) <= off)) (PreH28 : (off <= ((i + 1) * 1000000000))) (PreH29 : (((-i) * 1000000000) <= mind)) (PreH30 : (mind <= (0 : Int))) (PreH31 : (i <= (mind + (off - costA)))) (PreH32 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH33 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH34 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH35 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH36 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH37 : (ny = (candB - off))) (PreH38 : (((-(i + 1)) * 1000000000) <= ny)) (PreH39 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH40 : ((i + 1) <= (ny + off))) (PreH41 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH42 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH44 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  (int64Array.full d_pre (k_pre + 1) dp_2)
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  EX dp : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ ((i + 1) <= off) ” &&
  “ (off <= ((i + 1) * 1000000000)) ” &&
  “ (((-(i + 1)) * 1000000000) <= mind) ” &&
  “ (mind <= (0 : Int)) ” &&
  “ ((i + 1) <= (mind + off)) ” &&
  “ ((mind + off) <= ((i + 1) * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-(i + 1)) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= ((i + 1) * 1000000000))))) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp off mind) ”
  &&  (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
) \/
(
forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= (Znth y dp_2 (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog (0 : Int)))) (PreH14 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x ≠ y)) (PreH20 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH24 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH25 : (i <= (off - costA))) (PreH26 : ((off - costA) <= (i * 1000000000))) (PreH27 : ((i + 1) <= off)) (PreH28 : (off <= ((i + 1) * 1000000000))) (PreH29 : (((-i) * 1000000000) <= mind)) (PreH30 : (mind <= (0 : Int))) (PreH31 : (i <= (mind + (off - costA)))) (PreH32 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH33 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH34 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH35 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH36 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH37 : (ny = (candB - off))) (PreH38 : (((-(i + 1)) * 1000000000) <= ny)) (PreH39 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH40 : ((i + 1) <= (ny + off))) (PreH41 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH42 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH44 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  TT && emp 
|--
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-(i + 1)) * 1000000000) <= (Znth q_3 dp_2 (0 : Int))) ∧ ((Znth q_3 dp_2 (0 : Int)) <= ((i + 1) * 1000000000))))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ”
  &&  emp
)

noncomputable def solver_entail_wit_5_8_split_goal_1 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= (Znth y dp_2 (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog (0 : Int)))) (PreH14 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x ≠ y)) (PreH20 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH24 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH25 : (i <= (off - costA))) (PreH26 : ((off - costA) <= (i * 1000000000))) (PreH27 : ((i + 1) <= off)) (PreH28 : (off <= ((i + 1) * 1000000000))) (PreH29 : (((-i) * 1000000000) <= mind)) (PreH30 : (mind <= (0 : Int))) (PreH31 : (i <= (mind + (off - costA)))) (PreH32 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH33 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH34 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH35 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH36 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH37 : (ny = (candB - off))) (PreH38 : (((-(i + 1)) * 1000000000) <= ny)) (PreH39 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH40 : ((i + 1) <= (ny + off))) (PreH41 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH42 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH44 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-(i + 1)) * 1000000000) <= (Znth q_3 dp_2 (0 : Int))) ∧ ((Znth q_3 dp_2 (0 : Int)) <= ((i + 1) * 1000000000)))))

noncomputable def solver_entail_wit_5_8_split_goal_2 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= (Znth y dp_2 (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog (0 : Int)))) (PreH14 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x ≠ y)) (PreH20 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH24 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH25 : (i <= (off - costA))) (PreH26 : ((off - costA) <= (i * 1000000000))) (PreH27 : ((i + 1) <= off)) (PreH28 : (off <= ((i + 1) * 1000000000))) (PreH29 : (((-i) * 1000000000) <= mind)) (PreH30 : (mind <= (0 : Int))) (PreH31 : (i <= (mind + (off - costA)))) (PreH32 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH33 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH34 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH35 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH36 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH37 : (ny = (candB - off))) (PreH38 : (((-(i + 1)) * 1000000000) <= ny)) (PreH39 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH40 : ((i + 1) <= (ny + off))) (PreH41 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH42 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH44 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))

noncomputable def solver_entail_wit_5_8_split_goal_3 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= (Znth y dp_2 (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog (0 : Int)))) (PreH14 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x ≠ y)) (PreH20 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH24 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH25 : (i <= (off - costA))) (PreH26 : ((off - costA) <= (i * 1000000000))) (PreH27 : ((i + 1) <= off)) (PreH28 : (off <= ((i + 1) * 1000000000))) (PreH29 : (((-i) * 1000000000) <= mind)) (PreH30 : (mind <= (0 : Int))) (PreH31 : (i <= (mind + (off - costA)))) (PreH32 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH33 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH34 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH35 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH36 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH37 : (ny = (candB - off))) (PreH38 : (((-(i + 1)) * 1000000000) <= ny)) (PreH39 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH40 : ((i + 1) <= (ny + off))) (PreH41 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH42 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH44 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))

noncomputable def solver_entail_wit_5_9 : Prop :=
  (
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= (Znth y dp_2 (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog (0 : Int)))) (PreH14 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x ≠ y)) (PreH20 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH24 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH25 : (i <= (off - costA))) (PreH26 : ((off - costA) <= (i * 1000000000))) (PreH27 : ((i + 1) <= off)) (PreH28 : (off <= ((i + 1) * 1000000000))) (PreH29 : (((-i) * 1000000000) <= mind)) (PreH30 : (mind <= (0 : Int))) (PreH31 : (i <= (mind + (off - costA)))) (PreH32 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH33 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH34 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH35 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH36 : ((Znth x dp_2 (0 : Int)) < 4557430888798830399)) (PreH37 : (candB = (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH45 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  (int64Array.full d_pre (k_pre + 1) dp_2)
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  EX dp : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ ((i + 1) <= off) ” &&
  “ (off <= ((i + 1) * 1000000000)) ” &&
  “ (((-(i + 1)) * 1000000000) <= mind) ” &&
  “ (mind <= (0 : Int)) ” &&
  “ ((i + 1) <= (mind + off)) ” &&
  “ ((mind + off) <= ((i + 1) * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-(i + 1)) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= ((i + 1) * 1000000000))))) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp off mind) ”
  &&  (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
) \/
(
forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= (Znth y dp_2 (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog (0 : Int)))) (PreH14 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x ≠ y)) (PreH20 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH24 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH25 : (i <= (off - costA))) (PreH26 : ((off - costA) <= (i * 1000000000))) (PreH27 : ((i + 1) <= off)) (PreH28 : (off <= ((i + 1) * 1000000000))) (PreH29 : (((-i) * 1000000000) <= mind)) (PreH30 : (mind <= (0 : Int))) (PreH31 : (i <= (mind + (off - costA)))) (PreH32 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH33 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH34 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH35 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH36 : ((Znth x dp_2 (0 : Int)) < 4557430888798830399)) (PreH37 : (candB = (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH45 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  TT && emp 
|--
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-(i + 1)) * 1000000000) <= (Znth q_3 dp_2 (0 : Int))) ∧ ((Znth q_3 dp_2 (0 : Int)) <= ((i + 1) * 1000000000))))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ”
  &&  emp
)

noncomputable def solver_entail_wit_5_9_split_goal_1 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= (Znth y dp_2 (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog (0 : Int)))) (PreH14 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x ≠ y)) (PreH20 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH24 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH25 : (i <= (off - costA))) (PreH26 : ((off - costA) <= (i * 1000000000))) (PreH27 : ((i + 1) <= off)) (PreH28 : (off <= ((i + 1) * 1000000000))) (PreH29 : (((-i) * 1000000000) <= mind)) (PreH30 : (mind <= (0 : Int))) (PreH31 : (i <= (mind + (off - costA)))) (PreH32 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH33 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH34 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH35 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH36 : ((Znth x dp_2 (0 : Int)) < 4557430888798830399)) (PreH37 : (candB = (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH45 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-(i + 1)) * 1000000000) <= (Znth q_3 dp_2 (0 : Int))) ∧ ((Znth q_3 dp_2 (0 : Int)) <= ((i + 1) * 1000000000)))))

noncomputable def solver_entail_wit_5_9_split_goal_2 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= (Znth y dp_2 (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog (0 : Int)))) (PreH14 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x ≠ y)) (PreH20 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH24 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH25 : (i <= (off - costA))) (PreH26 : ((off - costA) <= (i * 1000000000))) (PreH27 : ((i + 1) <= off)) (PreH28 : (off <= ((i + 1) * 1000000000))) (PreH29 : (((-i) * 1000000000) <= mind)) (PreH30 : (mind <= (0 : Int))) (PreH31 : (i <= (mind + (off - costA)))) (PreH32 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH33 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH34 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH35 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH36 : ((Znth x dp_2 (0 : Int)) < 4557430888798830399)) (PreH37 : (candB = (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH45 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))

noncomputable def solver_entail_wit_5_9_split_goal_3 : Prop :=
  forall (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp_2 : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny >= (Znth y dp_2 (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q_4 : Int) , ((((0 : Int) <= q_4) ∧ (q_4 < n_pre)) -> ((1 <= (Znth q_4 prog (0 : Int))) ∧ ((Znth q_4 prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_5 : Int) , ((((0 : Int) <= q_5) ∧ (q_5 < k_pre)) -> (((1 <= (Znth q_5 hot_costs (0 : Int))) ∧ ((Znth q_5 hot_costs (0 : Int)) <= (Znth q_5 cold_costs (0 : Int)))) ∧ ((Znth q_5 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog (0 : Int)))) (PreH14 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x ≠ y)) (PreH20 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp_2)) = (k_pre + 1))) (PreH24 : ((Znth (0 : Int) dp_2 (0 : Int)) = (0 : Int))) (PreH25 : (i <= (off - costA))) (PreH26 : ((off - costA) <= (i * 1000000000))) (PreH27 : ((i + 1) <= off)) (PreH28 : (off <= ((i + 1) * 1000000000))) (PreH29 : (((-i) * 1000000000) <= mind)) (PreH30 : (mind <= (0 : Int))) (PreH31 : (i <= (mind + (off - costA)))) (PreH32 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH33 : forall (q_6 : Int) , ((((0 : Int) <= q_6) ∧ (q_6 <= k_pre)) -> (((Znth q_6 dp_2 (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_6 dp_2 (0 : Int))) ∧ ((Znth q_6 dp_2 (0 : Int)) <= (i * 1000000000)))))) (PreH34 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH35 : (((Znth x dp_2 (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH36 : ((Znth x dp_2 (0 : Int)) < 4557430888798830399)) (PreH37 : (candB = (((Znth x dp_2 (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp_2 (off - costA) mind)) (PreH43 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off ny))) (PreH44 : (((ny < (Znth y dp_2 (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp_2)) off mind))) (PreH45 : ((ny >= (Znth y dp_2 (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp_2 off mind))) ,
  forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (dp)) = (k_pre + 1))) (PreH14 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH15 : (i <= off)) (PreH16 : (off <= (i * 1000000000))) (PreH17 : (((-i) * 1000000000) <= mind)) (PreH18 : (mind <= (0 : Int))) (PreH19 : (i <= (mind + off))) (PreH20 : ((mind + off) <= (i * 1000000000))) (PreH21 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH22 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
|--
  “ (Spec prog cold_costs hot_costs (mind + off)) ”
  &&  (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full_shape d_pre (k_pre + 1))
) \/
(
forall (d_pre : Int) (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (dp)) = (k_pre + 1))) (PreH14 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH15 : (i <= off)) (PreH16 : (off <= (i * 1000000000))) (PreH17 : (((-i) * 1000000000) <= mind)) (PreH18 : (mind <= (0 : Int))) (PreH19 : (i <= (mind + off))) (PreH20 : ((mind + off) <= (i * 1000000000))) (PreH21 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH22 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full d_pre (k_pre + 1) dp)
|--
  “ (Spec prog cold_costs hot_costs (mind + off)) ”
  &&  (int64Array.full_shape d_pre (k_pre + 1))
)

noncomputable def solver_return_wit_1_split_goal_1 : Prop :=
  forall (d_pre : Int) (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (dp)) = (k_pre + 1))) (PreH14 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH15 : (i <= off)) (PreH16 : (off <= (i * 1000000000))) (PreH17 : (((-i) * 1000000000) <= mind)) (PreH18 : (mind <= (0 : Int))) (PreH19 : (i <= (mind + off))) (PreH20 : ((mind + off) <= (i * 1000000000))) (PreH21 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH22 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full d_pre (k_pre + 1) dp)
|--
  “ (Spec prog cold_costs hot_costs (mind + off)) ”

noncomputable def solver_return_wit_1_split_goal_spatial : Prop :=
  forall (d_pre : Int) (k_pre : Int) (n_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (dp)) = (k_pre + 1))) (PreH14 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH15 : (i <= off)) (PreH16 : (off <= (i * 1000000000))) (PreH17 : (((-i) * 1000000000) <= mind)) (PreH18 : (mind <= (0 : Int))) (PreH19 : (i <= (mind + off))) (PreH20 : ((mind + off) <= (i * 1000000000))) (PreH21 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH22 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full d_pre (k_pre + 1) dp)
|--
  (int64Array.full_shape d_pre (k_pre + 1))

noncomputable def solver_partial_solve_wit_1 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (initialized : (List Int)) (j : Int) (PreH1 : (j <= k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : ((0 : Int) <= j)) (PreH12 : (j <= (k_pre + 1))) (PreH13 : ((Zlength (initialized)) = j)) (PreH14 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 < j)) -> ((Znth q_3 initialized (0 : Int)) = 4557430888798830399))) ,
  (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.seg d_pre (0 : Int) j initialized)
  ** (int64Array.undef_seg d_pre j (k_pre + 1))
|--
  “ (j <= k_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (k_pre + 1)) ” &&
  “ ((Zlength (initialized)) = j) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 < j)) -> ((Znth q_3 initialized (0 : Int)) = 4557430888798830399)) ”
  &&  (((d_pre + (j * sizeof(INT64)))) # Int64 |->_)
  ** (int64Array.undef_seg d_pre (j + 1) (k_pre + 1))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.seg d_pre (0 : Int) j initialized)

noncomputable def solver_partial_solve_wit_2 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (initialized : (List Int)) (j : Int) (PreH1 : (j > k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : ((0 : Int) <= j)) (PreH12 : (j <= (k_pre + 1))) (PreH13 : ((Zlength (initialized)) = j)) (PreH14 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 < j)) -> ((Znth q_3 initialized (0 : Int)) = 4557430888798830399))) ,
  (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.seg d_pre (0 : Int) j initialized)
  ** (int64Array.undef_seg d_pre j (k_pre + 1))
|--
  “ (j > k_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (k_pre + 1)) ” &&
  “ ((Zlength (initialized)) = j) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 < j)) -> ((Znth q_3 initialized (0 : Int)) = 4557430888798830399)) ”
  &&  (((d_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |->_)
  ** (int64Array.missing_i d_pre (0 : Int) (0 : Int) j initialized)
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))

noncomputable def solver_partial_solve_wit_3 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (initialized : (List Int)) (j : Int) (PreH1 : (j > k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : ((0 : Int) <= j)) (PreH12 : (j <= (k_pre + 1))) (PreH13 : ((Zlength (initialized)) = j)) (PreH14 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 < j)) -> ((Znth q_3 initialized (0 : Int)) = 4557430888798830399))) ,
  (int64Array.full d_pre j (replace_Znth ((0 : Int)) ((0 : Int)) (initialized)))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  “ (j > k_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (k_pre + 1)) ” &&
  “ ((Zlength (initialized)) = j) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 < j)) -> ((Znth q_3 initialized (0 : Int)) = 4557430888798830399)) ”
  &&  (((a_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((Znth (0 : Int) prog (0 : Int))))
  ** (intArray.missing_i a_pre (0 : Int) (0 : Int) n_pre prog)
  ** (int64Array.full d_pre j (replace_Znth ((0 : Int)) ((0 : Int)) (initialized)))
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))

noncomputable def solver_partial_solve_wit_4 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (initialized : (List Int)) (j : Int) (PreH1 : (j > k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : ((0 : Int) <= j)) (PreH12 : (j <= (k_pre + 1))) (PreH13 : ((Zlength (initialized)) = j)) (PreH14 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 < j)) -> ((Znth q_3 initialized (0 : Int)) = 4557430888798830399))) ,
  (intArray.full a_pre n_pre prog)
  ** (int64Array.full d_pre j (replace_Znth ((0 : Int)) ((0 : Int)) (initialized)))
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  “ (j > k_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (k_pre + 1)) ” &&
  “ ((Zlength (initialized)) = j) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 < j)) -> ((Znth q_3 initialized (0 : Int)) = 4557430888798830399)) ”
  &&  (((cold_pre + ((Znth (0 : Int) prog (0 : Int)) * sizeof(INT64)))) # Int64 |-> ((Znth (Znth (0 : Int) prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  ** (int64Array.missing_i cold_pre (Znth (0 : Int) prog (0 : Int)) (0 : Int) (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full d_pre j (replace_Znth ((0 : Int)) ((0 : Int)) (initialized)))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))

noncomputable def solver_partial_solve_wit_5 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (dp)) = (k_pre + 1))) (PreH14 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH15 : (i <= off)) (PreH16 : (off <= (i * 1000000000))) (PreH17 : (((-i) * 1000000000) <= mind)) (PreH18 : (mind <= (0 : Int))) (PreH19 : (i <= (mind + off))) (PreH20 : ((mind + off) <= (i * 1000000000))) (PreH21 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH22 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
|--
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ (i <= off) ” &&
  “ (off <= (i * 1000000000)) ” &&
  “ (((-i) * 1000000000) <= mind) ” &&
  “ (mind <= (0 : Int)) ” &&
  “ (i <= (mind + off)) ” &&
  “ ((mind + off) <= (i * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000))))) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs i dp off mind) ”
  &&  (((a_pre + ((i - 1) * sizeof(INT)))) # Int |-> ((Znth (i - 1) prog (0 : Int))))
  ** (intArray.missing_i a_pre (i - 1) (0 : Int) n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)

noncomputable def solver_partial_solve_wit_6 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (dp)) = (k_pre + 1))) (PreH14 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH15 : (i <= off)) (PreH16 : (off <= (i * 1000000000))) (PreH17 : (((-i) * 1000000000) <= mind)) (PreH18 : (mind <= (0 : Int))) (PreH19 : (i <= (mind + off))) (PreH20 : ((mind + off) <= (i * 1000000000))) (PreH21 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH22 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
|--
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ (i <= off) ” &&
  “ (off <= (i * 1000000000)) ” &&
  “ (((-i) * 1000000000) <= mind) ” &&
  “ (mind <= (0 : Int)) ” &&
  “ (i <= (mind + off)) ” &&
  “ ((mind + off) <= (i * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000))))) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs i dp off mind) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i prog (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)

noncomputable def solver_partial_solve_wit_7 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((Zlength (dp)) = (k_pre + 1))) (PreH15 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH16 : (i <= off)) (PreH17 : (off <= (i * 1000000000))) (PreH18 : (((-i) * 1000000000) <= mind)) (PreH19 : (mind <= (0 : Int))) (PreH20 : (i <= (mind + off))) (PreH21 : ((mind + off) <= (i * 1000000000))) (PreH22 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH23 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
|--
  “ ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int))) ” &&
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ (i <= off) ” &&
  “ (off <= (i * 1000000000)) ” &&
  “ (((-i) * 1000000000) <= mind) ” &&
  “ (mind <= (0 : Int)) ” &&
  “ (i <= (mind + off)) ” &&
  “ ((mind + off) <= (i * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000))))) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs i dp off mind) ”
  &&  (((hot_pre + ((Znth i prog (0 : Int)) * sizeof(INT64)))) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  ** (int64Array.missing_i hot_pre (Znth i prog (0 : Int)) (0 : Int) (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)

noncomputable def solver_partial_solve_wit_8 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((Zlength (dp)) = (k_pre + 1))) (PreH15 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH16 : (i <= off)) (PreH17 : (off <= (i * 1000000000))) (PreH18 : (((-i) * 1000000000) <= mind)) (PreH19 : (mind <= (0 : Int))) (PreH20 : (i <= (mind + off))) (PreH21 : ((mind + off) <= (i * 1000000000))) (PreH22 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH23 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
|--
  “ ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int))) ” &&
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ (i <= off) ” &&
  “ (off <= (i * 1000000000)) ” &&
  “ (((-i) * 1000000000) <= mind) ” &&
  “ (mind <= (0 : Int)) ” &&
  “ (i <= (mind + off)) ” &&
  “ ((mind + off) <= (i * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000))))) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs i dp off mind) ”
  &&  (((cold_pre + ((Znth i prog (0 : Int)) * sizeof(INT64)))) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  ** (int64Array.missing_i cold_pre (Znth i prog (0 : Int)) (0 : Int) (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)

noncomputable def solver_partial_solve_wit_9 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((Zlength (dp)) = (k_pre + 1))) (PreH15 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH16 : (i <= off)) (PreH17 : (off <= (i * 1000000000))) (PreH18 : (((-i) * 1000000000) <= mind)) (PreH19 : (mind <= (0 : Int))) (PreH20 : (i <= (mind + off))) (PreH21 : ((mind + off) <= (i * 1000000000))) (PreH22 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH23 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
|--
  “ ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int))) ” &&
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ (i <= off) ” &&
  “ (off <= (i * 1000000000)) ” &&
  “ (((-i) * 1000000000) <= mind) ” &&
  “ (mind <= (0 : Int)) ” &&
  “ (i <= (mind + off)) ” &&
  “ ((mind + off) <= (i * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000))))) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs i dp off mind) ”
  &&  (((cold_pre + ((Znth i prog (0 : Int)) * sizeof(INT64)))) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  ** (int64Array.missing_i cold_pre (Znth i prog (0 : Int)) (0 : Int) (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full d_pre (k_pre + 1) dp)

noncomputable def solver_partial_solve_wit_10 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((Zlength (dp)) = (k_pre + 1))) (PreH15 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH16 : (i <= off)) (PreH17 : (off <= (i * 1000000000))) (PreH18 : (((-i) * 1000000000) <= mind)) (PreH19 : (mind <= (0 : Int))) (PreH20 : (i <= (mind + off))) (PreH21 : ((mind + off) <= (i * 1000000000))) (PreH22 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH23 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
|--
  “ ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int))) ” &&
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ (i <= off) ” &&
  “ (off <= (i * 1000000000)) ” &&
  “ (((-i) * 1000000000) <= mind) ” &&
  “ (mind <= (0 : Int)) ” &&
  “ (i <= (mind + off)) ” &&
  “ ((mind + off) <= (i * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000))))) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs i dp off mind) ”
  &&  (((cold_pre + ((Znth i prog (0 : Int)) * sizeof(INT64)))) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: cold_costs) (0 : Int))))
  ** (int64Array.missing_i cold_pre (Znth i prog (0 : Int)) (0 : Int) (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)

noncomputable def solver_partial_solve_wit_11 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((Zlength (dp)) = (k_pre + 1))) (PreH15 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH16 : (i <= off)) (PreH17 : (off <= (i * 1000000000))) (PreH18 : (((-i) * 1000000000) <= mind)) (PreH19 : (mind <= (0 : Int))) (PreH20 : (i <= (mind + off))) (PreH21 : ((mind + off) <= (i * 1000000000))) (PreH22 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH23 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full d_pre (k_pre + 1) dp)
|--
  “ ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int))) ” &&
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ (i <= off) ” &&
  “ (off <= (i * 1000000000)) ” &&
  “ (((-i) * 1000000000) <= mind) ” &&
  “ (mind <= (0 : Int)) ” &&
  “ (i <= (mind + off)) ” &&
  “ ((mind + off) <= (i * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000))))) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs i dp off mind) ”
  &&  (((d_pre + ((Znth i prog (0 : Int)) * sizeof(INT64)))) # Int64 |-> ((Znth (Znth i prog (0 : Int)) dp (0 : Int))))
  ** (int64Array.missing_i d_pre (Znth i prog (0 : Int)) (0 : Int) (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (intArray.full a_pre n_pre prog)

noncomputable def solver_partial_solve_wit_12 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 300000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (prog)))) (PreH8 : (k_pre = (Zlength (cold_costs)))) (PreH9 : (k_pre = (Zlength (hot_costs)))) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH11 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH12 : (1 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : ((Zlength (dp)) = (k_pre + 1))) (PreH15 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH16 : (i <= off)) (PreH17 : (off <= (i * 1000000000))) (PreH18 : (((-i) * 1000000000) <= mind)) (PreH19 : (mind <= (0 : Int))) (PreH20 : (i <= (mind + off))) (PreH21 : ((mind + off) <= (i * 1000000000))) (PreH22 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH23 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
|--
  “ ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int))) ” &&
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ (i <= off) ” &&
  “ (off <= (i * 1000000000)) ” &&
  “ (((-i) * 1000000000) <= mind) ” &&
  “ (mind <= (0 : Int)) ” &&
  “ (i <= (mind + off)) ” &&
  “ ((mind + off) <= (i * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000))))) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs i dp off mind) ”
  &&  (((d_pre + ((Znth i prog (0 : Int)) * sizeof(INT64)))) # Int64 |-> ((Znth (Znth i prog (0 : Int)) dp (0 : Int))))
  ** (int64Array.missing_i d_pre (Znth i prog (0 : Int)) (0 : Int) (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))

noncomputable def solver_partial_solve_wit_13 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH2 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH12 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1))) (PreH16 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000))) (PreH19 : (((-i) * 1000000000) <= mind)) (PreH20 : (mind <= (0 : Int))) (PreH21 : (i <= (mind + off))) (PreH22 : ((mind + off) <= (i * 1000000000))) (PreH23 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (intArray.full a_pre n_pre prog)
|--
  “ ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399) ” &&
  “ ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int))) ” &&
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ (i <= off) ” &&
  “ (off <= (i * 1000000000)) ” &&
  “ (((-i) * 1000000000) <= mind) ” &&
  “ (mind <= (0 : Int)) ” &&
  “ (i <= (mind + off)) ” &&
  “ ((mind + off) <= (i * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000))))) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs i dp off mind) ”
  &&  (((d_pre + ((Znth i prog (0 : Int)) * sizeof(INT64)))) # Int64 |-> ((Znth (Znth i prog (0 : Int)) dp (0 : Int))))
  ** (int64Array.missing_i d_pre (Znth i prog (0 : Int)) (0 : Int) (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (intArray.full a_pre n_pre prog)

noncomputable def solver_partial_solve_wit_14 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH2 : ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int)))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH12 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1))) (PreH16 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000))) (PreH19 : (((-i) * 1000000000) <= mind)) (PreH20 : (mind <= (0 : Int))) (PreH21 : (i <= (mind + off))) (PreH22 : ((mind + off) <= (i * 1000000000))) (PreH23 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (intArray.full a_pre n_pre prog)
|--
  “ ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399) ” &&
  “ ((Znth i prog (0 : Int)) = (Znth (i - 1) prog (0 : Int))) ” &&
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ (i <= off) ” &&
  “ (off <= (i * 1000000000)) ” &&
  “ (((-i) * 1000000000) <= mind) ” &&
  “ (mind <= (0 : Int)) ” &&
  “ (i <= (mind + off)) ” &&
  “ ((mind + off) <= (i * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000))))) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs i dp off mind) ”
  &&  (((hot_pre + ((Znth i prog (0 : Int)) * sizeof(INT64)))) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  ** (int64Array.missing_i hot_pre (Znth i prog (0 : Int)) (0 : Int) (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (intArray.full a_pre n_pre prog)

noncomputable def solver_partial_solve_wit_15 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH2 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH12 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1))) (PreH16 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000))) (PreH19 : (((-i) * 1000000000) <= mind)) (PreH20 : (mind <= (0 : Int))) (PreH21 : (i <= (mind + off))) (PreH22 : ((mind + off) <= (i * 1000000000))) (PreH23 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  “ ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399) ” &&
  “ ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int))) ” &&
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ (i <= off) ” &&
  “ (off <= (i * 1000000000)) ” &&
  “ (((-i) * 1000000000) <= mind) ” &&
  “ (mind <= (0 : Int)) ” &&
  “ (i <= (mind + off)) ” &&
  “ ((mind + off) <= (i * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000))))) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs i dp off mind) ”
  &&  (((d_pre + ((Znth i prog (0 : Int)) * sizeof(INT64)))) # Int64 |-> ((Znth (Znth i prog (0 : Int)) dp (0 : Int))))
  ** (int64Array.missing_i d_pre (Znth i prog (0 : Int)) (0 : Int) (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))

noncomputable def solver_partial_solve_wit_16 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (mind : Int) (off : Int) (dp : (List Int)) (i : Int) (PreH1 : ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399)) (PreH2 : ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int)))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 300000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (prog)))) (PreH9 : (k_pre = (Zlength (cold_costs)))) (PreH10 : (k_pre = (Zlength (hot_costs)))) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH12 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : ((Zlength (dp)) = (k_pre + 1))) (PreH16 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH17 : (i <= off)) (PreH18 : (off <= (i * 1000000000))) (PreH19 : (((-i) * 1000000000) <= mind)) (PreH20 : (mind <= (0 : Int))) (PreH21 : (i <= (mind + off))) (PreH22 : ((mind + off) <= (i * 1000000000))) (PreH23 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH24 : (NormalizedScheduleState prog cold_costs hot_costs i dp off mind)) ,
  (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  “ ((Znth (Znth i prog (0 : Int)) dp (0 : Int)) < 4557430888798830399) ” &&
  “ ((Znth i prog (0 : Int)) ≠ (Znth (i - 1) prog (0 : Int))) ” &&
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ (i <= off) ” &&
  “ (off <= (i * 1000000000)) ” &&
  “ (((-i) * 1000000000) <= mind) ” &&
  “ (mind <= (0 : Int)) ” &&
  “ (i <= (mind + off)) ” &&
  “ ((mind + off) <= (i * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000))))) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs i dp off mind) ”
  &&  (((hot_pre + ((Znth i prog (0 : Int)) * sizeof(INT64)))) # Int64 |-> ((Znth (Znth i prog (0 : Int)) ((0 : Int) :: hot_costs) (0 : Int))))
  ** (int64Array.missing_i hot_pre (Znth i prog (0 : Int)) (0 : Int) (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (intArray.full a_pre n_pre prog)

noncomputable def solver_partial_solve_wit_17 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 300000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 300000)) (PreH5 : (n_pre = (Zlength (prog)))) (PreH6 : (k_pre = (Zlength (cold_costs)))) (PreH7 : (k_pre = (Zlength (hot_costs)))) (PreH8 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH9 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH10 : (1 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (x = (Znth i prog (0 : Int)))) (PreH13 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH14 : (1 <= x)) (PreH15 : (x <= k_pre)) (PreH16 : (1 <= y)) (PreH17 : (y <= k_pre)) (PreH18 : (x = y)) (PreH19 : (costA = (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))) (PreH20 : (1 <= costA)) (PreH21 : (costA <= 1000000000)) (PreH22 : ((Zlength (dp)) = (k_pre + 1))) (PreH23 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH24 : (i <= (off - costA))) (PreH25 : ((off - costA) <= (i * 1000000000))) (PreH26 : ((i + 1) <= off)) (PreH27 : (off <= ((i + 1) * 1000000000))) (PreH28 : (((-i) * 1000000000) <= mind)) (PreH29 : (mind <= (0 : Int))) (PreH30 : (i <= (mind + (off - costA)))) (PreH31 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH32 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH33 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH34 : (((Znth x dp (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH35 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (ny = (candB - off))) (PreH37 : (((-(i + 1)) * 1000000000) <= ny)) (PreH38 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH39 : ((i + 1) <= (ny + off))) (PreH40 : (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA) mind)) (PreH41 : (((ny < (Znth y dp (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off ny))) (PreH42 : (((ny < (Znth y dp (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off mind))) (PreH43 : ((ny >= (Znth y dp (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp off mind))) ,
  (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ (x = (Znth i prog (0 : Int))) ” &&
  “ (y = (Znth (i - 1) prog (0 : Int))) ” &&
  “ (1 <= x) ” &&
  “ (x <= k_pre) ” &&
  “ (1 <= y) ” &&
  “ (y <= k_pre) ” &&
  “ (x = y) ” &&
  “ (costA = (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))) ” &&
  “ (1 <= costA) ” &&
  “ (costA <= 1000000000) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ (i <= (off - costA)) ” &&
  “ ((off - costA) <= (i * 1000000000)) ” &&
  “ ((i + 1) <= off) ” &&
  “ (off <= ((i + 1) * 1000000000)) ” &&
  “ (((-i) * 1000000000) <= mind) ” &&
  “ (mind <= (0 : Int)) ” &&
  “ (i <= (mind + (off - costA))) ” &&
  “ ((mind + (off - costA)) <= (i * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000))))) ” &&
  “ (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) ” &&
  “ (((Znth x dp (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) ” &&
  “ (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) ” &&
  “ (ny = (candB - off)) ” &&
  “ (((-(i + 1)) * 1000000000) <= ny) ” &&
  “ ((ny + off) <= ((i + 1) * 1000000000)) ” &&
  “ ((i + 1) <= (ny + off)) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA) mind) ” &&
  “ (((ny < (Znth y dp (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off ny)) ” &&
  “ (((ny < (Znth y dp (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off mind)) ” &&
  “ ((ny >= (Znth y dp (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp off mind)) ”
  &&  (((d_pre + (y * sizeof(INT64)))) # Int64 |-> ((Znth y dp (0 : Int))))
  ** (int64Array.missing_i d_pre y (0 : Int) (k_pre + 1) dp)
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))

noncomputable def solver_partial_solve_wit_18 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 300000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 300000)) (PreH5 : (n_pre = (Zlength (prog)))) (PreH6 : (k_pre = (Zlength (cold_costs)))) (PreH7 : (k_pre = (Zlength (hot_costs)))) (PreH8 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH9 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH10 : (1 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (x = (Znth i prog (0 : Int)))) (PreH13 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH14 : (1 <= x)) (PreH15 : (x <= k_pre)) (PreH16 : (1 <= y)) (PreH17 : (y <= k_pre)) (PreH18 : (x = y)) (PreH19 : (costA = (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))) (PreH20 : (1 <= costA)) (PreH21 : (costA <= 1000000000)) (PreH22 : ((Zlength (dp)) = (k_pre + 1))) (PreH23 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH24 : (i <= (off - costA))) (PreH25 : ((off - costA) <= (i * 1000000000))) (PreH26 : ((i + 1) <= off)) (PreH27 : (off <= ((i + 1) * 1000000000))) (PreH28 : (((-i) * 1000000000) <= mind)) (PreH29 : (mind <= (0 : Int))) (PreH30 : (i <= (mind + (off - costA)))) (PreH31 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH32 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH33 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH34 : (((Znth x dp (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH35 : ((Znth x dp (0 : Int)) < 4557430888798830399)) (PreH36 : (candB = (((Znth x dp (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) (PreH37 : (ny = (candB - off))) (PreH38 : (((-(i + 1)) * 1000000000) <= ny)) (PreH39 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH40 : ((i + 1) <= (ny + off))) (PreH41 : (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA) mind)) (PreH42 : (((ny < (Znth y dp (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off ny))) (PreH43 : (((ny < (Znth y dp (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off mind))) (PreH44 : ((ny >= (Znth y dp (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp off mind))) ,
  (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ (x = (Znth i prog (0 : Int))) ” &&
  “ (y = (Znth (i - 1) prog (0 : Int))) ” &&
  “ (1 <= x) ” &&
  “ (x <= k_pre) ” &&
  “ (1 <= y) ” &&
  “ (y <= k_pre) ” &&
  “ (x = y) ” &&
  “ (costA = (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))) ” &&
  “ (1 <= costA) ” &&
  “ (costA <= 1000000000) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ (i <= (off - costA)) ” &&
  “ ((off - costA) <= (i * 1000000000)) ” &&
  “ ((i + 1) <= off) ” &&
  “ (off <= ((i + 1) * 1000000000)) ” &&
  “ (((-i) * 1000000000) <= mind) ” &&
  “ (mind <= (0 : Int)) ” &&
  “ (i <= (mind + (off - costA))) ” &&
  “ ((mind + (off - costA)) <= (i * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000))))) ” &&
  “ (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) ” &&
  “ (((Znth x dp (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) ” &&
  “ ((Znth x dp (0 : Int)) < 4557430888798830399) ” &&
  “ (candB = (((Znth x dp (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))) ” &&
  “ (ny = (candB - off)) ” &&
  “ (((-(i + 1)) * 1000000000) <= ny) ” &&
  “ ((ny + off) <= ((i + 1) * 1000000000)) ” &&
  “ ((i + 1) <= (ny + off)) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA) mind) ” &&
  “ (((ny < (Znth y dp (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off ny)) ” &&
  “ (((ny < (Znth y dp (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off mind)) ” &&
  “ ((ny >= (Znth y dp (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp off mind)) ”
  &&  (((d_pre + (y * sizeof(INT64)))) # Int64 |-> ((Znth y dp (0 : Int))))
  ** (int64Array.missing_i d_pre y (0 : Int) (k_pre + 1) dp)
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))

noncomputable def solver_partial_solve_wit_19 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 300000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 300000)) (PreH5 : (n_pre = (Zlength (prog)))) (PreH6 : (k_pre = (Zlength (cold_costs)))) (PreH7 : (k_pre = (Zlength (hot_costs)))) (PreH8 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH9 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH10 : (1 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (x = (Znth i prog (0 : Int)))) (PreH13 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH14 : (1 <= x)) (PreH15 : (x <= k_pre)) (PreH16 : (1 <= y)) (PreH17 : (y <= k_pre)) (PreH18 : (x ≠ y)) (PreH19 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH20 : (1 <= costA)) (PreH21 : (costA <= 1000000000)) (PreH22 : ((Zlength (dp)) = (k_pre + 1))) (PreH23 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH24 : (i <= (off - costA))) (PreH25 : ((off - costA) <= (i * 1000000000))) (PreH26 : ((i + 1) <= off)) (PreH27 : (off <= ((i + 1) * 1000000000))) (PreH28 : (((-i) * 1000000000) <= mind)) (PreH29 : (mind <= (0 : Int))) (PreH30 : (i <= (mind + (off - costA)))) (PreH31 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH32 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH33 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH34 : (((Znth x dp (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH35 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH36 : (ny = (candB - off))) (PreH37 : (((-(i + 1)) * 1000000000) <= ny)) (PreH38 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH39 : ((i + 1) <= (ny + off))) (PreH40 : (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA) mind)) (PreH41 : (((ny < (Znth y dp (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off ny))) (PreH42 : (((ny < (Znth y dp (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off mind))) (PreH43 : ((ny >= (Znth y dp (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp off mind))) ,
  (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ (x = (Znth i prog (0 : Int))) ” &&
  “ (y = (Znth (i - 1) prog (0 : Int))) ” &&
  “ (1 <= x) ” &&
  “ (x <= k_pre) ” &&
  “ (1 <= y) ” &&
  “ (y <= k_pre) ” &&
  “ (x ≠ y) ” &&
  “ (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))) ” &&
  “ (1 <= costA) ” &&
  “ (costA <= 1000000000) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ (i <= (off - costA)) ” &&
  “ ((off - costA) <= (i * 1000000000)) ” &&
  “ ((i + 1) <= off) ” &&
  “ (off <= ((i + 1) * 1000000000)) ” &&
  “ (((-i) * 1000000000) <= mind) ” &&
  “ (mind <= (0 : Int)) ” &&
  “ (i <= (mind + (off - costA))) ” &&
  “ ((mind + (off - costA)) <= (i * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000))))) ” &&
  “ (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) ” &&
  “ (((Znth x dp (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) ” &&
  “ (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) ” &&
  “ (ny = (candB - off)) ” &&
  “ (((-(i + 1)) * 1000000000) <= ny) ” &&
  “ ((ny + off) <= ((i + 1) * 1000000000)) ” &&
  “ ((i + 1) <= (ny + off)) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA) mind) ” &&
  “ (((ny < (Znth y dp (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off ny)) ” &&
  “ (((ny < (Znth y dp (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off mind)) ” &&
  “ ((ny >= (Znth y dp (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp off mind)) ”
  &&  (((d_pre + (y * sizeof(INT64)))) # Int64 |-> ((Znth y dp (0 : Int))))
  ** (int64Array.missing_i d_pre y (0 : Int) (k_pre + 1) dp)
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))

noncomputable def solver_partial_solve_wit_20 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 300000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 300000)) (PreH5 : (n_pre = (Zlength (prog)))) (PreH6 : (k_pre = (Zlength (cold_costs)))) (PreH7 : (k_pre = (Zlength (hot_costs)))) (PreH8 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH9 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH10 : (1 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (x = (Znth i prog (0 : Int)))) (PreH13 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH14 : (1 <= x)) (PreH15 : (x <= k_pre)) (PreH16 : (1 <= y)) (PreH17 : (y <= k_pre)) (PreH18 : (x ≠ y)) (PreH19 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH20 : (1 <= costA)) (PreH21 : (costA <= 1000000000)) (PreH22 : ((Zlength (dp)) = (k_pre + 1))) (PreH23 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH24 : (i <= (off - costA))) (PreH25 : ((off - costA) <= (i * 1000000000))) (PreH26 : ((i + 1) <= off)) (PreH27 : (off <= ((i + 1) * 1000000000))) (PreH28 : (((-i) * 1000000000) <= mind)) (PreH29 : (mind <= (0 : Int))) (PreH30 : (i <= (mind + (off - costA)))) (PreH31 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH32 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH33 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH34 : (((Znth x dp (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH35 : ((Znth x dp (0 : Int)) < 4557430888798830399)) (PreH36 : (candB = (((Znth x dp (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) (PreH37 : (ny = (candB - off))) (PreH38 : (((-(i + 1)) * 1000000000) <= ny)) (PreH39 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH40 : ((i + 1) <= (ny + off))) (PreH41 : (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA) mind)) (PreH42 : (((ny < (Znth y dp (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off ny))) (PreH43 : (((ny < (Znth y dp (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off mind))) (PreH44 : ((ny >= (Znth y dp (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp off mind))) ,
  (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
  ** (int64Array.full d_pre (k_pre + 1) dp)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ (x = (Znth i prog (0 : Int))) ” &&
  “ (y = (Znth (i - 1) prog (0 : Int))) ” &&
  “ (1 <= x) ” &&
  “ (x <= k_pre) ” &&
  “ (1 <= y) ” &&
  “ (y <= k_pre) ” &&
  “ (x ≠ y) ” &&
  “ (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))) ” &&
  “ (1 <= costA) ” &&
  “ (costA <= 1000000000) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ (i <= (off - costA)) ” &&
  “ ((off - costA) <= (i * 1000000000)) ” &&
  “ ((i + 1) <= off) ” &&
  “ (off <= ((i + 1) * 1000000000)) ” &&
  “ (((-i) * 1000000000) <= mind) ” &&
  “ (mind <= (0 : Int)) ” &&
  “ (i <= (mind + (off - costA))) ” &&
  “ ((mind + (off - costA)) <= (i * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000))))) ” &&
  “ (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) ” &&
  “ (((Znth x dp (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) ” &&
  “ ((Znth x dp (0 : Int)) < 4557430888798830399) ” &&
  “ (candB = (((Znth x dp (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))) ” &&
  “ (ny = (candB - off)) ” &&
  “ (((-(i + 1)) * 1000000000) <= ny) ” &&
  “ ((ny + off) <= ((i + 1) * 1000000000)) ” &&
  “ ((i + 1) <= (ny + off)) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA) mind) ” &&
  “ (((ny < (Znth y dp (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off ny)) ” &&
  “ (((ny < (Znth y dp (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off mind)) ” &&
  “ ((ny >= (Znth y dp (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp off mind)) ”
  &&  (((d_pre + (y * sizeof(INT64)))) # Int64 |-> ((Znth y dp (0 : Int))))
  ** (int64Array.missing_i d_pre y (0 : Int) (k_pre + 1) dp)
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))

noncomputable def solver_partial_solve_wit_21 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny < (Znth y dp (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog (0 : Int)))) (PreH14 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x = y)) (PreH20 : (costA = (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp)) = (k_pre + 1))) (PreH24 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH25 : (i <= (off - costA))) (PreH26 : ((off - costA) <= (i * 1000000000))) (PreH27 : ((i + 1) <= off)) (PreH28 : (off <= ((i + 1) * 1000000000))) (PreH29 : (((-i) * 1000000000) <= mind)) (PreH30 : (mind <= (0 : Int))) (PreH31 : (i <= (mind + (off - costA)))) (PreH32 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH33 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH34 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH35 : (((Znth x dp (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH36 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH37 : (ny = (candB - off))) (PreH38 : (((-(i + 1)) * 1000000000) <= ny)) (PreH39 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH40 : ((i + 1) <= (ny + off))) (PreH41 : (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA) mind)) (PreH42 : (((ny < (Znth y dp (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off ny))) (PreH43 : (((ny < (Znth y dp (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off mind))) (PreH44 : ((ny >= (Znth y dp (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp off mind))) ,
  (int64Array.full d_pre (k_pre + 1) dp)
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  “ (ny < (Znth y dp (0 : Int))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ (x = (Znth i prog (0 : Int))) ” &&
  “ (y = (Znth (i - 1) prog (0 : Int))) ” &&
  “ (1 <= x) ” &&
  “ (x <= k_pre) ” &&
  “ (1 <= y) ” &&
  “ (y <= k_pre) ” &&
  “ (x = y) ” &&
  “ (costA = (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))) ” &&
  “ (1 <= costA) ” &&
  “ (costA <= 1000000000) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ (i <= (off - costA)) ” &&
  “ ((off - costA) <= (i * 1000000000)) ” &&
  “ ((i + 1) <= off) ” &&
  “ (off <= ((i + 1) * 1000000000)) ” &&
  “ (((-i) * 1000000000) <= mind) ” &&
  “ (mind <= (0 : Int)) ” &&
  “ (i <= (mind + (off - costA))) ” &&
  “ ((mind + (off - costA)) <= (i * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000))))) ” &&
  “ (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) ” &&
  “ (((Znth x dp (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) ” &&
  “ (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) ” &&
  “ (ny = (candB - off)) ” &&
  “ (((-(i + 1)) * 1000000000) <= ny) ” &&
  “ ((ny + off) <= ((i + 1) * 1000000000)) ” &&
  “ ((i + 1) <= (ny + off)) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA) mind) ” &&
  “ (((ny < (Znth y dp (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off ny)) ” &&
  “ (((ny < (Znth y dp (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off mind)) ” &&
  “ ((ny >= (Znth y dp (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp off mind)) ”
  &&  (((d_pre + (y * sizeof(INT64)))) # Int64 |->_)
  ** (int64Array.missing_i d_pre y (0 : Int) (k_pre + 1) dp)
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))

noncomputable def solver_partial_solve_wit_22 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny < (Znth y dp (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog (0 : Int)))) (PreH14 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x ≠ y)) (PreH20 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp)) = (k_pre + 1))) (PreH24 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH25 : (i <= (off - costA))) (PreH26 : ((off - costA) <= (i * 1000000000))) (PreH27 : ((i + 1) <= off)) (PreH28 : (off <= ((i + 1) * 1000000000))) (PreH29 : (((-i) * 1000000000) <= mind)) (PreH30 : (mind <= (0 : Int))) (PreH31 : (i <= (mind + (off - costA)))) (PreH32 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH33 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH34 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH35 : (((Znth x dp (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH36 : (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH37 : (ny = (candB - off))) (PreH38 : (((-(i + 1)) * 1000000000) <= ny)) (PreH39 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH40 : ((i + 1) <= (ny + off))) (PreH41 : (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA) mind)) (PreH42 : (((ny < (Znth y dp (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off ny))) (PreH43 : (((ny < (Znth y dp (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off mind))) (PreH44 : ((ny >= (Znth y dp (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp off mind))) ,
  (int64Array.full d_pre (k_pre + 1) dp)
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  “ (ny < (Znth y dp (0 : Int))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ (x = (Znth i prog (0 : Int))) ” &&
  “ (y = (Znth (i - 1) prog (0 : Int))) ” &&
  “ (1 <= x) ” &&
  “ (x <= k_pre) ” &&
  “ (1 <= y) ” &&
  “ (y <= k_pre) ” &&
  “ (x ≠ y) ” &&
  “ (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))) ” &&
  “ (1 <= costA) ” &&
  “ (costA <= 1000000000) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ (i <= (off - costA)) ” &&
  “ ((off - costA) <= (i * 1000000000)) ” &&
  “ ((i + 1) <= off) ” &&
  “ (off <= ((i + 1) * 1000000000)) ” &&
  “ (((-i) * 1000000000) <= mind) ” &&
  “ (mind <= (0 : Int)) ” &&
  “ (i <= (mind + (off - costA))) ” &&
  “ ((mind + (off - costA)) <= (i * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000))))) ” &&
  “ (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) ” &&
  “ (((Znth x dp (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) ” &&
  “ (candB = ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) ” &&
  “ (ny = (candB - off)) ” &&
  “ (((-(i + 1)) * 1000000000) <= ny) ” &&
  “ ((ny + off) <= ((i + 1) * 1000000000)) ” &&
  “ ((i + 1) <= (ny + off)) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA) mind) ” &&
  “ (((ny < (Znth y dp (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off ny)) ” &&
  “ (((ny < (Znth y dp (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off mind)) ” &&
  “ ((ny >= (Znth y dp (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp off mind)) ”
  &&  (((d_pre + (y * sizeof(INT64)))) # Int64 |->_)
  ** (int64Array.missing_i d_pre y (0 : Int) (k_pre + 1) dp)
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))

noncomputable def solver_partial_solve_wit_23 : Prop :=
  forall (d_pre : Int) (hot_pre : Int) (cold_pre : Int) (k_pre : Int) (n_pre : Int) (a_pre : Int) (hot_costs : (List Int)) (cold_costs : (List Int)) (prog : (List Int)) (dp : (List Int)) (i : Int) (x : Int) (y : Int) (costA : Int) (off : Int) (mind : Int) (candB : Int) (ny : Int) (PreH1 : (ny < (Znth y dp (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 300000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 300000)) (PreH6 : (n_pre = (Zlength (prog)))) (PreH7 : (k_pre = (Zlength (cold_costs)))) (PreH8 : (k_pre = (Zlength (hot_costs)))) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre)))) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (x = (Znth i prog (0 : Int)))) (PreH14 : (y = (Znth (i - 1) prog (0 : Int)))) (PreH15 : (1 <= x)) (PreH16 : (x <= k_pre)) (PreH17 : (1 <= y)) (PreH18 : (y <= k_pre)) (PreH19 : (x ≠ y)) (PreH20 : (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) (PreH21 : (1 <= costA)) (PreH22 : (costA <= 1000000000)) (PreH23 : ((Zlength (dp)) = (k_pre + 1))) (PreH24 : ((Znth (0 : Int) dp (0 : Int)) = (0 : Int))) (PreH25 : (i <= (off - costA))) (PreH26 : ((off - costA) <= (i * 1000000000))) (PreH27 : ((i + 1) <= off)) (PreH28 : (off <= ((i + 1) * 1000000000))) (PreH29 : (((-i) * 1000000000) <= mind)) (PreH30 : (mind <= (0 : Int))) (PreH31 : (i <= (mind + (off - costA)))) (PreH32 : ((mind + (off - costA)) <= (i * 1000000000))) (PreH33 : forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000)))))) (PreH34 : (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))))) (PreH35 : (((Znth x dp (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))))) (PreH36 : ((Znth x dp (0 : Int)) < 4557430888798830399)) (PreH37 : (candB = (((Znth x dp (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) (PreH38 : (ny = (candB - off))) (PreH39 : (((-(i + 1)) * 1000000000) <= ny)) (PreH40 : ((ny + off) <= ((i + 1) * 1000000000))) (PreH41 : ((i + 1) <= (ny + off))) (PreH42 : (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA) mind)) (PreH43 : (((ny < (Znth y dp (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off ny))) (PreH44 : (((ny < (Znth y dp (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off mind))) (PreH45 : ((ny >= (Znth y dp (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp off mind))) ,
  (int64Array.full d_pre (k_pre + 1) dp)
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))
|--
  “ (ny < (Znth y dp (0 : Int))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 300000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 300000) ” &&
  “ (n_pre = (Zlength (prog))) ” &&
  “ (k_pre = (Zlength (cold_costs))) ” &&
  “ (k_pre = (Zlength (hot_costs))) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < n_pre)) -> ((1 <= (Znth q prog (0 : Int))) ∧ ((Znth q prog (0 : Int)) <= k_pre))) ” &&
  “ forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < k_pre)) -> (((1 <= (Znth q_2 hot_costs (0 : Int))) ∧ ((Znth q_2 hot_costs (0 : Int)) <= (Znth q_2 cold_costs (0 : Int)))) ∧ ((Znth q_2 cold_costs (0 : Int)) <= 1000000000))) ” &&
  “ (1 <= i) ” &&
  “ (i < n_pre) ” &&
  “ (x = (Znth i prog (0 : Int))) ” &&
  “ (y = (Znth (i - 1) prog (0 : Int))) ” &&
  “ (1 <= x) ” &&
  “ (x <= k_pre) ” &&
  “ (1 <= y) ” &&
  “ (y <= k_pre) ” &&
  “ (x ≠ y) ” &&
  “ (costA = (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int)))) ” &&
  “ (1 <= costA) ” &&
  “ (costA <= 1000000000) ” &&
  “ ((Zlength (dp)) = (k_pre + 1)) ” &&
  “ ((Znth (0 : Int) dp (0 : Int)) = (0 : Int)) ” &&
  “ (i <= (off - costA)) ” &&
  “ ((off - costA) <= (i * 1000000000)) ” &&
  “ ((i + 1) <= off) ” &&
  “ (off <= ((i + 1) * 1000000000)) ” &&
  “ (((-i) * 1000000000) <= mind) ” &&
  “ (mind <= (0 : Int)) ” &&
  “ (i <= (mind + (off - costA))) ” &&
  “ ((mind + (off - costA)) <= (i * 1000000000)) ” &&
  “ forall (q_3 : Int) , ((((0 : Int) <= q_3) ∧ (q_3 <= k_pre)) -> (((Znth q_3 dp (0 : Int)) = 4557430888798830399) ∨ ((((-i) * 1000000000) <= (Znth q_3 dp (0 : Int))) ∧ ((Znth q_3 dp (0 : Int)) <= (i * 1000000000))))) ” &&
  “ (candB <= ((mind + (off - costA)) + (Znth (x) (((0 : Int) :: cold_costs)) ((0 : Int))))) ” &&
  “ (((Znth x dp (0 : Int)) < 4557430888798830399) -> (candB <= (((Znth x dp (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int)))))) ” &&
  “ ((Znth x dp (0 : Int)) < 4557430888798830399) ” &&
  “ (candB = (((Znth x dp (0 : Int)) + (off - costA)) + (Znth (x) (((0 : Int) :: hot_costs)) ((0 : Int))))) ” &&
  “ (ny = (candB - off)) ” &&
  “ (((-(i + 1)) * 1000000000) <= ny) ” &&
  “ ((ny + off) <= ((i + 1) * 1000000000)) ” &&
  “ ((i + 1) <= (ny + off)) ” &&
  “ (NormalizedScheduleState prog cold_costs hot_costs i dp (off - costA) mind) ” &&
  “ (((ny < (Znth y dp (0 : Int))) ∧ (ny < mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off ny)) ” &&
  “ (((ny < (Znth y dp (0 : Int))) ∧ (ny >= mind)) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) (replace_Znth (y) (ny) (dp)) off mind)) ” &&
  “ ((ny >= (Znth y dp (0 : Int))) -> (NormalizedScheduleState prog cold_costs hot_costs (i + 1) dp off mind)) ”
  &&  (((d_pre + (y * sizeof(INT64)))) # Int64 |->_)
  ** (int64Array.missing_i d_pre y (0 : Int) (k_pre + 1) dp)
  ** (intArray.full a_pre n_pre prog)
  ** (int64Array.full cold_pre (k_pre + 1) ((0 : Int) :: cold_costs))
  ** (int64Array.full hot_pre (k_pre + 1) ((0 : Int) :: hot_costs))


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
  proof_of_solver_safety_wit_12 : solver_safety_wit_12
  proof_of_solver_safety_wit_14 : solver_safety_wit_14
  proof_of_solver_safety_wit_15 : solver_safety_wit_15
  proof_of_solver_safety_wit_16 : solver_safety_wit_16
  proof_of_solver_safety_wit_18 : solver_safety_wit_18
  proof_of_solver_safety_wit_20 : solver_safety_wit_20
  proof_of_solver_safety_wit_27 : solver_safety_wit_27
  proof_of_solver_safety_wit_30 : solver_safety_wit_30
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
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2
  proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3
  proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4
  proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5
  proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6
  proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7
  proof_of_solver_partial_solve_wit_8 : solver_partial_solve_wit_8
  proof_of_solver_partial_solve_wit_9 : solver_partial_solve_wit_9
  proof_of_solver_partial_solve_wit_10 : solver_partial_solve_wit_10
  proof_of_solver_partial_solve_wit_11 : solver_partial_solve_wit_11
  proof_of_solver_partial_solve_wit_12 : solver_partial_solve_wit_12
  proof_of_solver_partial_solve_wit_13 : solver_partial_solve_wit_13
  proof_of_solver_partial_solve_wit_14 : solver_partial_solve_wit_14
  proof_of_solver_partial_solve_wit_15 : solver_partial_solve_wit_15
  proof_of_solver_partial_solve_wit_16 : solver_partial_solve_wit_16
  proof_of_solver_partial_solve_wit_17 : solver_partial_solve_wit_17
  proof_of_solver_partial_solve_wit_18 : solver_partial_solve_wit_18
  proof_of_solver_partial_solve_wit_19 : solver_partial_solve_wit_19
  proof_of_solver_partial_solve_wit_20 : solver_partial_solve_wit_20
  proof_of_solver_partial_solve_wit_21 : solver_partial_solve_wit_21
  proof_of_solver_partial_solve_wit_22 : solver_partial_solve_wit_22
  proof_of_solver_partial_solve_wit_23 : solver_partial_solve_wit_23
  proof_of_solver_safety_wit_11 : solver_safety_wit_11
  proof_of_solver_safety_wit_13 : solver_safety_wit_13
  proof_of_solver_safety_wit_17 : solver_safety_wit_17
  proof_of_solver_safety_wit_19 : solver_safety_wit_19
  proof_of_solver_safety_wit_21 : solver_safety_wit_21
  proof_of_solver_safety_wit_22 : solver_safety_wit_22
  proof_of_solver_safety_wit_23 : solver_safety_wit_23
  proof_of_solver_safety_wit_24 : solver_safety_wit_24
  proof_of_solver_safety_wit_25 : solver_safety_wit_25
  proof_of_solver_safety_wit_26 : solver_safety_wit_26
  proof_of_solver_safety_wit_28 : solver_safety_wit_28
  proof_of_solver_safety_wit_29 : solver_safety_wit_29
  proof_of_solver_safety_wit_31 : solver_safety_wit_31
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_2 : solver_entail_wit_2
  proof_of_solver_entail_wit_3 : solver_entail_wit_3
  proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1
  proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2
  proof_of_solver_entail_wit_4_3 : solver_entail_wit_4_3
  proof_of_solver_entail_wit_4_4 : solver_entail_wit_4_4
  proof_of_solver_entail_wit_4_5 : solver_entail_wit_4_5
  proof_of_solver_entail_wit_4_6 : solver_entail_wit_4_6
  proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1
  proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2
  proof_of_solver_entail_wit_5_3 : solver_entail_wit_5_3
  proof_of_solver_entail_wit_5_4 : solver_entail_wit_5_4
  proof_of_solver_entail_wit_5_5 : solver_entail_wit_5_5
  proof_of_solver_entail_wit_5_6 : solver_entail_wit_5_6
  proof_of_solver_entail_wit_5_7 : solver_entail_wit_5_7
  proof_of_solver_entail_wit_5_8 : solver_entail_wit_5_8
  proof_of_solver_entail_wit_5_9 : solver_entail_wit_5_9
  proof_of_solver_return_wit_1 : solver_return_wit_1

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P073_1799D2_hot_start_up_goal
