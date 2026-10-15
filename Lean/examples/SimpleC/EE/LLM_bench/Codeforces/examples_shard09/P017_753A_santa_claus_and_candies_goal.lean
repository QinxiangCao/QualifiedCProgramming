import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P017_753A_santa_claus_and_candies_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P017_753A_santa_claus_and_candies_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P017_753A_santa_claus_and_candies_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P017_753A_santa_claus_and_candies_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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
  forall (out_pre : Int) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) ,
  ((( &( "k" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (intArray.undef_full out_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) ,
  ((( &( "used" ) )) # Int64 |->_)
  ** ((( &( "k" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (intArray.undef_full out_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (used : Int) (k : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= k)) (PreH4 : (k <= n_pre)) (PreH5 : (used = (triangular (k)))) (PreH6 : ((0 : Int) <= used)) (PreH7 : (used <= n_pre)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "used" ) )) # Int64 |-> (used))
  ** (intArray.undef_full out_pre n_pre)
|--
  “ ((used + (k + 1)) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (used + (k + 1))) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (used : Int) (k : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= k)) (PreH4 : (k <= n_pre)) (PreH5 : (used = (triangular (k)))) (PreH6 : ((0 : Int) <= used)) (PreH7 : (used <= n_pre)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "used" ) )) # Int64 |-> (used))
  ** (intArray.undef_full out_pre n_pre)
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (used : Int) (k : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= k)) (PreH4 : (k <= n_pre)) (PreH5 : (used = (triangular (k)))) (PreH6 : ((0 : Int) <= used)) (PreH7 : (used <= n_pre)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "used" ) )) # Int64 |-> (used))
  ** (intArray.undef_full out_pre n_pre)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (used : Int) (k : Int) (PreH1 : ((used + (k + 1)) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : ((0 : Int) <= used)) (PreH8 : (used <= n_pre)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "used" ) )) # Int64 |-> (used))
  ** (intArray.undef_full out_pre n_pre)
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def solver_safety_wit_7 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (used : Int) (k : Int) (PreH1 : ((used + (k + 1)) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : ((0 : Int) <= used)) (PreH8 : (used <= n_pre)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "k" ) )) # Int |-> ((k + 1)))
  ** ((( &( "used" ) )) # Int64 |-> (used))
  ** (intArray.undef_full out_pre n_pre)
|--
  “ ((used + (k + 1)) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (used + (k + 1))) ”

noncomputable def solver_safety_wit_8 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (used : Int) (k : Int) (PreH1 : ((used + (k + 1)) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : ((0 : Int) <= used)) (PreH8 : (used <= n_pre)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "used" ) )) # Int64 |-> (used))
  ** (intArray.undef_full out_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_9 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (written : (List Int)) (i : Int) (used : Int) (k : Int) (PreH1 : (i < k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : ((0 : Int) <= used)) (PreH8 : (used <= n_pre)) (PreH9 : (n_pre < (used + (k + 1)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= k)) (PreH12 : (CandyPrefix i written)) ,
  (intArray.seg out_pre (0 : Int) (i + 1) (written ++ ((i + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg out_pre (i + 1) n_pre)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "used" ) )) # Int64 |-> (used))
  ** ((( &( "i" ) )) # Int |-> (i))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_10 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (written : (List Int)) (i : Int) (used : Int) (k : Int) (PreH1 : (i < k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : ((0 : Int) <= used)) (PreH8 : (used <= n_pre)) (PreH9 : (n_pre < (used + (k + 1)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= k)) (PreH12 : (CandyPrefix i written)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "used" ) )) # Int64 |-> (used))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.seg out_pre (0 : Int) i written)
  ** (intArray.undef_seg out_pre i n_pre)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_11 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (written : (List Int)) (i : Int) (used : Int) (k : Int) (PreH1 : (i < k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : ((0 : Int) <= used)) (PreH8 : (used <= n_pre)) (PreH9 : (n_pre < (used + (k + 1)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= k)) (PreH12 : (CandyPrefix i written)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "used" ) )) # Int64 |-> (used))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.seg out_pre (0 : Int) i written)
  ** (intArray.undef_seg out_pre i n_pre)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_12 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (written : (List Int)) (i : Int) (used : Int) (k : Int) (PreH1 : (i >= k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : ((0 : Int) <= used)) (PreH8 : (used <= n_pre)) (PreH9 : (n_pre < (used + (k + 1)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= k)) (PreH12 : (CandyPrefix i written)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "used" ) )) # Int64 |-> (used))
  ** (intArray.seg out_pre (0 : Int) i written)
  ** (intArray.undef_seg out_pre i n_pre)
|--
  “ ((k - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k - 1)) ”

noncomputable def solver_safety_wit_13 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (written : (List Int)) (i : Int) (used : Int) (k : Int) (PreH1 : (i >= k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : ((0 : Int) <= used)) (PreH8 : (used <= n_pre)) (PreH9 : (n_pre < (used + (k + 1)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= k)) (PreH12 : (CandyPrefix i written)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "used" ) )) # Int64 |-> (used))
  ** (intArray.seg out_pre (0 : Int) i written)
  ** (intArray.undef_seg out_pre i n_pre)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_14 : Prop :=
  (
forall (out_pre : Int) (n_pre : Int) (written : (List Int)) (i : Int) (used : Int) (k : Int) (PreH1 : (i >= k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : ((0 : Int) <= used)) (PreH8 : (used <= n_pre)) (PreH9 : (n_pre < (used + (k + 1)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= k)) (PreH12 : (CandyPrefix i written)) ,
  (intArray.seg out_pre (0 : Int) i written)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "used" ) )) # Int64 |-> (used))
  ** (intArray.undef_seg out_pre i n_pre)
|--
  “ (((Znth ((k - 1) - (0 : Int)) written (0 : Int)) + (n_pre - used)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth ((k - 1) - (0 : Int)) written (0 : Int)) + (n_pre - used))) ”
) \/
(
forall (out_pre : Int) (n_pre : Int) (written : (List Int)) (i : Int) (used : Int) (k : Int) (PreH1 : (i >= k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : ((0 : Int) <= used)) (PreH8 : (used <= n_pre)) (PreH9 : (n_pre < (used + (k + 1)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= k)) (PreH12 : (CandyPrefix i written)) ,
  (intArray.seg out_pre (0 : Int) i written)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "used" ) )) # Int64 |-> (used))
  ** (intArray.undef_seg out_pre i n_pre)
|--
  “ (((Znth ((k - 1) - (0 : Int)) written (0 : Int)) + (n_pre - used)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth ((k - 1) - (0 : Int)) written (0 : Int)) + (n_pre - used))) ”
)

noncomputable def solver_safety_wit_14_split_goal_1 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (written : (List Int)) (i : Int) (used : Int) (k : Int) (PreH1 : (i >= k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : ((0 : Int) <= used)) (PreH8 : (used <= n_pre)) (PreH9 : (n_pre < (used + (k + 1)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= k)) (PreH12 : (CandyPrefix i written)) ,
  (intArray.seg out_pre (0 : Int) i written)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "used" ) )) # Int64 |-> (used))
  ** (intArray.undef_seg out_pre i n_pre)
|--
  “ (((Znth ((k - 1) - (0 : Int)) written (0 : Int)) + (n_pre - used)) <= INT_MAX) ”

noncomputable def solver_safety_wit_14_split_goal_2 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (written : (List Int)) (i : Int) (used : Int) (k : Int) (PreH1 : (i >= k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : ((0 : Int) <= used)) (PreH8 : (used <= n_pre)) (PreH9 : (n_pre < (used + (k + 1)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= k)) (PreH12 : (CandyPrefix i written)) ,
  (intArray.seg out_pre (0 : Int) i written)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "used" ) )) # Int64 |-> (used))
  ** (intArray.undef_seg out_pre i n_pre)
|--
  “ ((INT_MIN) <= ((Znth ((k - 1) - (0 : Int)) written (0 : Int)) + (n_pre - used))) ”

noncomputable def solver_safety_wit_15 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (written : (List Int)) (i : Int) (used : Int) (k : Int) (PreH1 : (i >= k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : ((0 : Int) <= used)) (PreH8 : (used <= n_pre)) (PreH9 : (n_pre < (used + (k + 1)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= k)) (PreH12 : (CandyPrefix i written)) ,
  (intArray.seg out_pre (0 : Int) i written)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "used" ) )) # Int64 |-> (used))
  ** (intArray.undef_seg out_pre i n_pre)
|--
  “ ((n_pre - used) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (n_pre - used)) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (out_pre : Int) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) ,
  (intArray.undef_full out_pre n_pre)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) = (triangular ((0 : Int)))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ”
  &&  (intArray.undef_full out_pre n_pre)
) \/
(
forall (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) ,
  TT && emp 
|--
  “ ((0 : Int) = (triangular ((0 : Int)))) ”
  &&  emp
)

noncomputable def solver_entail_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) ,
  ((0 : Int) = (triangular ((0 : Int))))

noncomputable def solver_entail_wit_2 : Prop :=
  (
forall (out_pre : Int) (n_pre : Int) (used : Int) (k : Int) (PreH1 : ((used + (k + 1)) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : ((0 : Int) <= used)) (PreH8 : (used <= n_pre)) ,
  (intArray.undef_full out_pre n_pre)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= (k + 1)) ” &&
  “ ((k + 1) <= n_pre) ” &&
  “ ((used + (k + 1)) = (triangular ((k + 1)))) ” &&
  “ ((0 : Int) <= (used + (k + 1))) ” &&
  “ ((used + (k + 1)) <= n_pre) ”
  &&  (intArray.undef_full out_pre n_pre)
) \/
(
forall (n_pre : Int) (used : Int) (k : Int) (PreH1 : ((used + (k + 1)) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : ((0 : Int) <= used)) (PreH8 : (used <= n_pre)) ,
  TT && emp 
|--
  “ ((used + (k + 1)) = (triangular ((k + 1)))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (used : Int) (k : Int) (PreH1 : ((used + (k + 1)) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : ((0 : Int) <= used)) (PreH8 : (used <= n_pre)) ,
  ((used + (k + 1)) = (triangular ((k + 1))))

noncomputable def solver_entail_wit_3 : Prop :=
  (
forall (out_pre : Int) (n_pre : Int) (used : Int) (k : Int) (PreH1 : ((used + (k + 1)) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : ((0 : Int) <= used)) (PreH8 : (used <= n_pre)) ,
  (intArray.undef_full out_pre n_pre)
|--
  EX written : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (1 <= k) ” &&
  “ (k <= n_pre) ” &&
  “ (used = (triangular (k))) ” &&
  “ ((0 : Int) <= used) ” &&
  “ (used <= n_pre) ” &&
  “ (n_pre < (used + (k + 1))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (CandyPrefix (0 : Int) written) ”
  &&  (intArray.seg out_pre (0 : Int) (0 : Int) written)
  ** (intArray.undef_seg out_pre (0 : Int) n_pre)
) \/
(
forall (n_pre : Int) (used : Int) (k : Int) (PreH1 : ((used + (k + 1)) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : ((0 : Int) <= used)) (PreH8 : (used <= n_pre)) ,
  TT && emp 
|--
  “ (CandyPrefix (0 : Int) (@List.nil Int)) ” &&
  “ (1 <= k) ”
  &&  emp
)

noncomputable def solver_entail_wit_3_split_goal_1 : Prop :=
  forall (n_pre : Int) (used : Int) (k : Int) (PreH1 : ((used + (k + 1)) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : ((0 : Int) <= used)) (PreH8 : (used <= n_pre)) ,
  (CandyPrefix (0 : Int) (@List.nil Int))

noncomputable def solver_entail_wit_3_split_goal_2 : Prop :=
  forall (n_pre : Int) (used : Int) (k : Int) (PreH1 : ((used + (k + 1)) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : ((0 : Int) <= used)) (PreH8 : (used <= n_pre)) ,
  (1 <= k)

noncomputable def solver_entail_wit_4 : Prop :=
  (
forall (out_pre : Int) (n_pre : Int) (written_2 : (List Int)) (i : Int) (used : Int) (k : Int) (PreH1 : (i < k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : ((0 : Int) <= used)) (PreH8 : (used <= n_pre)) (PreH9 : (n_pre < (used + (k + 1)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= k)) (PreH12 : (CandyPrefix i written_2)) ,
  (intArray.seg out_pre (0 : Int) (i + 1) (written_2 ++ ((i + 1) :: (@List.nil Int))))
  ** (intArray.undef_seg out_pre (i + 1) n_pre)
|--
  EX written : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (1 <= k) ” &&
  “ (k <= n_pre) ” &&
  “ (used = (triangular (k))) ” &&
  “ ((0 : Int) <= used) ” &&
  “ (used <= n_pre) ” &&
  “ (n_pre < (used + (k + 1))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= k) ” &&
  “ (CandyPrefix (i + 1) written) ”
  &&  (intArray.seg out_pre (0 : Int) (i + 1) written)
  ** (intArray.undef_seg out_pre (i + 1) n_pre)
) \/
(
forall (n_pre : Int) (written_2 : (List Int)) (i : Int) (used : Int) (k : Int) (PreH1 : (i < k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : ((0 : Int) <= used)) (PreH8 : (used <= n_pre)) (PreH9 : (n_pre < (used + (k + 1)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= k)) (PreH12 : (CandyPrefix i written_2)) ,
  TT && emp 
|--
  “ (CandyPrefix (i + 1) (written_2 ++ ((i + 1) :: (@List.nil Int)))) ”
  &&  emp
)

noncomputable def solver_entail_wit_4_split_goal_1 : Prop :=
  forall (n_pre : Int) (written_2 : (List Int)) (i : Int) (used : Int) (k : Int) (PreH1 : (i < k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : ((0 : Int) <= used)) (PreH8 : (used <= n_pre)) (PreH9 : (n_pre < (used + (k + 1)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= k)) (PreH12 : (CandyPrefix i written_2)) ,
  (CandyPrefix (i + 1) (written_2 ++ ((i + 1) :: (@List.nil Int))))

noncomputable def solver_entail_wit_5 : Prop :=
  (
forall (out_pre : Int) (n_pre : Int) (written : (List Int)) (i : Int) (used : Int) (k : Int) (PreH1 : (i >= k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : ((0 : Int) <= used)) (PreH8 : (used <= n_pre)) (PreH9 : (n_pre < (used + (k + 1)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= k)) (PreH12 : (CandyPrefix i written)) ,
  (intArray.full out_pre i (replace_Znth ((k - 1)) (((Znth ((k - 1) - (0 : Int)) written (0 : Int)) + (n_pre - used))) (written)))
  ** (intArray.undef_seg out_pre i n_pre)
|--
  EX out_spec : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (1 <= k) ” &&
  “ (k <= n_pre) ” &&
  “ (used = (triangular (k))) ” &&
  “ ((0 : Int) <= used) ” &&
  “ (used <= n_pre) ” &&
  “ (n_pre < (used + (k + 1))) ” &&
  “ (GreedyCandyPlan n_pre k out_spec) ” &&
  “ (Spec n_pre out_spec) ”
  &&  (intArray.full out_pre k out_spec)
  ** (intArray.undef_seg out_pre k n_pre)
) \/
(
forall (out_pre : Int) (n_pre : Int) (written : (List Int)) (i : Int) (used : Int) (k : Int) (PreH1 : (i >= k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : ((0 : Int) <= used)) (PreH8 : (used <= n_pre)) (PreH9 : (n_pre < (used + (k + 1)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= k)) (PreH12 : (CandyPrefix i written)) ,
  (intArray.full out_pre i (replace_Znth ((k - 1)) (((Znth ((k - 1) - (0 : Int)) written (0 : Int)) + (n_pre - used))) (written)))
|--
  EX out_spec : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (1 <= k) ” &&
  “ (k <= n_pre) ” &&
  “ (used = (triangular (k))) ” &&
  “ ((0 : Int) <= used) ” &&
  “ (used <= n_pre) ” &&
  “ (n_pre < (used + (k + 1))) ” &&
  “ (GreedyCandyPlan n_pre k out_spec) ” &&
  “ (Spec n_pre out_spec) ”
  &&  (intArray.full out_pre k out_spec)
)

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (out_pre : Int) (n_pre : Int) (out_spec_2 : (List Int)) (k : Int) (used : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (1 <= k)) (PreH4 : (k <= n_pre)) (PreH5 : (used = (triangular (k)))) (PreH6 : ((0 : Int) <= used)) (PreH7 : (used <= n_pre)) (PreH8 : (n_pre < (used + (k + 1)))) (PreH9 : (GreedyCandyPlan n_pre k out_spec_2)) (PreH10 : (Spec n_pre out_spec_2)) ,
  (intArray.full out_pre k out_spec_2)
  ** (intArray.undef_seg out_pre k n_pre)
|--
  EX out_spec : (List Int),
  “ (Spec n_pre out_spec) ” &&
  “ (k = (Zlength (out_spec))) ”
  &&  (intArray.full out_pre (Zlength (out_spec)) out_spec)
  ** (intArray.undef_seg out_pre (Zlength (out_spec)) n_pre)
) \/
(
forall (out_pre : Int) (n_pre : Int) (out_spec_2 : (List Int)) (k : Int) (used : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (1 <= k)) (PreH4 : (k <= n_pre)) (PreH5 : (used = (triangular (k)))) (PreH6 : ((0 : Int) <= used)) (PreH7 : (used <= n_pre)) (PreH8 : (n_pre < (used + (k + 1)))) (PreH9 : (GreedyCandyPlan n_pre k out_spec_2)) (PreH10 : (Spec n_pre out_spec_2)) ,
  (intArray.full out_pre k out_spec_2)
  ** (intArray.undef_seg out_pre k n_pre)
|--
  EX out_spec : (List Int),
  “ (Spec n_pre out_spec) ” &&
  “ (k = (Zlength (out_spec))) ”
  &&  (intArray.full out_pre (Zlength (out_spec)) out_spec)
  ** (intArray.undef_seg out_pre (Zlength (out_spec)) n_pre)
)

noncomputable def solver_partial_solve_wit_1 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (written : (List Int)) (i : Int) (used : Int) (k : Int) (PreH1 : (i < k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : ((0 : Int) <= used)) (PreH8 : (used <= n_pre)) (PreH9 : (n_pre < (used + (k + 1)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= k)) (PreH12 : (CandyPrefix i written)) ,
  (intArray.seg out_pre (0 : Int) i written)
  ** (intArray.undef_seg out_pre i n_pre)
|--
  “ (i < k) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (1 <= k) ” &&
  “ (k <= n_pre) ” &&
  “ (used = (triangular (k))) ” &&
  “ ((0 : Int) <= used) ” &&
  “ (used <= n_pre) ” &&
  “ (n_pre < (used + (k + 1))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= k) ” &&
  “ (CandyPrefix i written) ”
  &&  (((out_pre + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg out_pre (i + 1) n_pre)
  ** (intArray.seg out_pre (0 : Int) i written)

noncomputable def solver_partial_solve_wit_2 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (written : (List Int)) (i : Int) (used : Int) (k : Int) (PreH1 : (i >= k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : ((0 : Int) <= used)) (PreH8 : (used <= n_pre)) (PreH9 : (n_pre < (used + (k + 1)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= k)) (PreH12 : (CandyPrefix i written)) ,
  (intArray.seg out_pre (0 : Int) i written)
  ** (intArray.undef_seg out_pre i n_pre)
|--
  “ (i >= k) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (1 <= k) ” &&
  “ (k <= n_pre) ” &&
  “ (used = (triangular (k))) ” &&
  “ ((0 : Int) <= used) ” &&
  “ (used <= n_pre) ” &&
  “ (n_pre < (used + (k + 1))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= k) ” &&
  “ (CandyPrefix i written) ”
  &&  (((out_pre + ((k - 1) * sizeof(INT)))) # Int |-> ((Znth ((k - 1) - (0 : Int)) written (0 : Int))))
  ** (intArray.missing_i out_pre (k - 1) (0 : Int) i written)
  ** (intArray.undef_seg out_pre i n_pre)

noncomputable def solver_partial_solve_wit_3 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (written : (List Int)) (i : Int) (used : Int) (k : Int) (PreH1 : (i >= k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : ((0 : Int) <= used)) (PreH8 : (used <= n_pre)) (PreH9 : (n_pre < (used + (k + 1)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= k)) (PreH12 : (CandyPrefix i written)) ,
  (intArray.seg out_pre (0 : Int) i written)
  ** (intArray.undef_seg out_pre i n_pre)
|--
  “ (i >= k) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (1 <= k) ” &&
  “ (k <= n_pre) ” &&
  “ (used = (triangular (k))) ” &&
  “ ((0 : Int) <= used) ” &&
  “ (used <= n_pre) ” &&
  “ (n_pre < (used + (k + 1))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= k) ” &&
  “ (CandyPrefix i written) ”
  &&  (((out_pre + ((k - 1) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i out_pre (k - 1) (0 : Int) i written)
  ** (intArray.undef_seg out_pre i n_pre)


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
  proof_of_solver_safety_wit_15 : solver_safety_wit_15
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2
  proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3
  proof_of_solver_safety_wit_14 : solver_safety_wit_14
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_2 : solver_entail_wit_2
  proof_of_solver_entail_wit_3 : solver_entail_wit_3
  proof_of_solver_entail_wit_4 : solver_entail_wit_4
  proof_of_solver_entail_wit_5 : solver_entail_wit_5
  proof_of_solver_return_wit_1 : solver_return_wit_1

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P017_753A_santa_claus_and_candies_goal
