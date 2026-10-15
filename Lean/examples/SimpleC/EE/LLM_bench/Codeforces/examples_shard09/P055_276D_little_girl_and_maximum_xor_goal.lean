import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P055_276D_little_girl_and_maximum_xor_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P055_276D_little_girl_and_maximum_xor_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P055_276D_little_girl_and_maximum_xor_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P055_276D_little_girl_and_maximum_xor_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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
  forall (r_pre : Int) (l_pre : Int) (PreH1 : (1 <= l_pre)) (PreH2 : (l_pre <= r_pre)) (PreH3 : (r_pre <= 1000000000000000000)) ,
  ((( &( "x" ) )) # UInt64 |-> ((Z.lxor l_pre r_pre)))
  ** ((( &( "l" ) )) # UInt64 |-> (l_pre))
  ** ((( &( "r" ) )) # UInt64 |-> (r_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (r_pre : Int) (l_pre : Int) (PreH1 : ((Z.lxor l_pre r_pre) = (0 : Int))) (PreH2 : (1 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= 1000000000000000000)) ,
  ((( &( "x" ) )) # UInt64 |-> ((Z.lxor l_pre r_pre)))
  ** ((( &( "l" ) )) # UInt64 |-> (l_pre))
  ** ((( &( "r" ) )) # UInt64 |-> (r_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (r_pre : Int) (l_pre : Int) (PreH1 : ((Z.lxor l_pre r_pre) ≠ (0 : Int))) (PreH2 : (1 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= 1000000000000000000)) ,
  ((( &( "b" ) )) # Int |->_)
  ** ((( &( "x" ) )) # UInt64 |-> ((Z.lxor l_pre r_pre)))
  ** ((( &( "l" ) )) # UInt64 |-> (l_pre))
  ** ((( &( "r" ) )) # UInt64 |-> (r_pre))
|--
  “ (63 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 63) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (r_pre : Int) (l_pre : Int) (b : Int) (x : Int) (PreH1 : (1 <= l_pre)) (PreH2 : (l_pre <= r_pre)) (PreH3 : (r_pre <= 1000000000000000000)) (PreH4 : ((0 : Int) < x)) (PreH5 : (x <= 18446744073709551615)) (PreH6 : ((0 : Int) <= b)) (PreH7 : (b <= 63)) (PreH8 : (HighestBitScan l_pre r_pre x b)) ,
  ((( &( "l" ) )) # UInt64 |-> (l_pre))
  ** ((( &( "r" ) )) # UInt64 |-> (r_pre))
  ** ((( &( "x" ) )) # UInt64 |-> (x))
  ** ((( &( "b" ) )) # Int |-> (b))
|--
  “ (b <= 63) ” &&
  “ ((0 : Int) <= b) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (r_pre : Int) (l_pre : Int) (b : Int) (x : Int) (PreH1 : ((Z.land (Z.shiftr x b) 1) = (0 : Int))) (PreH2 : (1 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= 1000000000000000000)) (PreH5 : ((0 : Int) < x)) (PreH6 : (x <= 18446744073709551615)) (PreH7 : ((0 : Int) <= b)) (PreH8 : (b <= 63)) (PreH9 : (HighestBitScan l_pre r_pre x b)) ,
  ((( &( "l" ) )) # UInt64 |-> (l_pre))
  ** ((( &( "r" ) )) # UInt64 |-> (r_pre))
  ** ((( &( "x" ) )) # UInt64 |-> (x))
  ** ((( &( "b" ) )) # Int |-> (b))
|--
  “ ((b - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (b - 1)) ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (r_pre : Int) (l_pre : Int) (b : Int) (x : Int) (PreH1 : ((Z.land (Z.shiftr x b) 1) ≠ (0 : Int))) (PreH2 : (1 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= 1000000000000000000)) (PreH5 : ((0 : Int) < x)) (PreH6 : (x <= 18446744073709551615)) (PreH7 : ((0 : Int) <= b)) (PreH8 : (b <= 63)) (PreH9 : (HighestBitScan l_pre r_pre x b)) ,
  ((( &( "l" ) )) # UInt64 |-> (l_pre))
  ** ((( &( "r" ) )) # UInt64 |-> (r_pre))
  ** ((( &( "x" ) )) # UInt64 |-> (x))
  ** ((( &( "b" ) )) # Int |-> (b))
|--
  “ (63 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 63) ”

noncomputable def solver_safety_wit_7 : Prop :=
  forall (r_pre : Int) (l_pre : Int) (b : Int) (x : Int) (PreH1 : (b ≠ 63)) (PreH2 : ((Z.land (Z.shiftr x b) 1) ≠ (0 : Int))) (PreH3 : (1 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : (r_pre <= 1000000000000000000)) (PreH6 : ((0 : Int) < x)) (PreH7 : (x <= 18446744073709551615)) (PreH8 : ((0 : Int) <= b)) (PreH9 : (b <= 63)) (PreH10 : (HighestBitScan l_pre r_pre x b)) ,
  ((( &( "l" ) )) # UInt64 |-> (l_pre))
  ** ((( &( "r" ) )) # UInt64 |-> (r_pre))
  ** ((( &( "x" ) )) # UInt64 |-> (x))
  ** ((( &( "b" ) )) # Int |-> (b))
|--
  “ ((b + 1) <= 63) ” &&
  “ ((0 : Int) <= (b + 1)) ”

noncomputable def solver_safety_wit_8 : Prop :=
  forall (r_pre : Int) (l_pre : Int) (b : Int) (x : Int) (PreH1 : (b ≠ 63)) (PreH2 : ((Z.land (Z.shiftr x b) 1) ≠ (0 : Int))) (PreH3 : (1 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : (r_pre <= 1000000000000000000)) (PreH6 : ((0 : Int) < x)) (PreH7 : (x <= 18446744073709551615)) (PreH8 : ((0 : Int) <= b)) (PreH9 : (b <= 63)) (PreH10 : (HighestBitScan l_pre r_pre x b)) ,
  ((( &( "l" ) )) # UInt64 |-> (l_pre))
  ** ((( &( "r" ) )) # UInt64 |-> (r_pre))
  ** ((( &( "x" ) )) # UInt64 |-> (x))
  ** ((( &( "b" ) )) # Int |-> (b))
|--
  “ ((b + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (b + 1)) ”

noncomputable def solver_safety_wit_9 : Prop :=
  forall (r_pre : Int) (l_pre : Int) (b : Int) (x : Int) (PreH1 : (b ≠ 63)) (PreH2 : ((Z.land (Z.shiftr x b) 1) ≠ (0 : Int))) (PreH3 : (1 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : (r_pre <= 1000000000000000000)) (PreH6 : ((0 : Int) < x)) (PreH7 : (x <= 18446744073709551615)) (PreH8 : ((0 : Int) <= b)) (PreH9 : (b <= 63)) (PreH10 : (HighestBitScan l_pre r_pre x b)) ,
  ((( &( "l" ) )) # UInt64 |-> (l_pre))
  ** ((( &( "r" ) )) # UInt64 |-> (r_pre))
  ** ((( &( "x" ) )) # UInt64 |-> (x))
  ** ((( &( "b" ) )) # Int |-> (b))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_10 : Prop :=
  forall (r_pre : Int) (l_pre : Int) (b : Int) (x : Int) (PreH1 : (b ≠ 63)) (PreH2 : ((Z.land (Z.shiftr x b) 1) ≠ (0 : Int))) (PreH3 : (1 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : (r_pre <= 1000000000000000000)) (PreH6 : ((0 : Int) < x)) (PreH7 : (x <= 18446744073709551615)) (PreH8 : ((0 : Int) <= b)) (PreH9 : (b <= 63)) (PreH10 : (HighestBitScan l_pre r_pre x b)) ,
  ((( &( "l" ) )) # UInt64 |-> (l_pre))
  ** ((( &( "r" ) )) # UInt64 |-> (r_pre))
  ** ((( &( "x" ) )) # UInt64 |-> (x))
  ** ((( &( "b" ) )) # Int |-> (b))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (r_pre : Int) (l_pre : Int) (PreH1 : ((Z.lxor l_pre r_pre) ≠ (0 : Int))) (PreH2 : (1 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= 1000000000000000000)) ,
  TT && emp 
|--
  “ (1 <= l_pre) ” &&
  “ (l_pre <= r_pre) ” &&
  “ (r_pre <= 1000000000000000000) ” &&
  “ ((0 : Int) < (Z.lxor l_pre r_pre)) ” &&
  “ ((Z.lxor l_pre r_pre) <= 18446744073709551615) ” &&
  “ ((0 : Int) <= 63) ” &&
  “ (63 <= 63) ” &&
  “ (HighestBitScan l_pre r_pre (Z.lxor l_pre r_pre) 63) ”
  &&  emp
) \/
(
forall (r_pre : Int) (l_pre : Int) (PreH1 : ((Z.lxor l_pre r_pre) ≠ (0 : Int))) (PreH2 : (1 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= 1000000000000000000)) ,
  TT && emp 
|--
  “ (HighestBitScan l_pre r_pre (Z.lxor l_pre r_pre) 63) ” &&
  “ ((Z.lxor l_pre r_pre) <= 18446744073709551615) ” &&
  “ ((0 : Int) < (Z.lxor l_pre r_pre)) ”
  &&  emp
)

noncomputable def solver_entail_wit_1_split_goal_1 : Prop :=
  forall (r_pre : Int) (l_pre : Int) (PreH1 : ((Z.lxor l_pre r_pre) ≠ (0 : Int))) (PreH2 : (1 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= 1000000000000000000)) ,
  (HighestBitScan l_pre r_pre (Z.lxor l_pre r_pre) 63)

noncomputable def solver_entail_wit_1_split_goal_2 : Prop :=
  forall (r_pre : Int) (l_pre : Int) (PreH1 : ((Z.lxor l_pre r_pre) ≠ (0 : Int))) (PreH2 : (1 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= 1000000000000000000)) ,
  ((Z.lxor l_pre r_pre) <= 18446744073709551615)

noncomputable def solver_entail_wit_1_split_goal_3 : Prop :=
  forall (r_pre : Int) (l_pre : Int) (PreH1 : ((Z.lxor l_pre r_pre) ≠ (0 : Int))) (PreH2 : (1 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= 1000000000000000000)) ,
  ((0 : Int) < (Z.lxor l_pre r_pre))

noncomputable def solver_entail_wit_2 : Prop :=
  (
forall (r_pre : Int) (l_pre : Int) (b : Int) (x : Int) (PreH1 : ((Z.land (Z.shiftr x b) 1) = (0 : Int))) (PreH2 : (1 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= 1000000000000000000)) (PreH5 : ((0 : Int) < x)) (PreH6 : (x <= 18446744073709551615)) (PreH7 : ((0 : Int) <= b)) (PreH8 : (b <= 63)) (PreH9 : (HighestBitScan l_pre r_pre x b)) ,
  TT && emp 
|--
  “ (1 <= l_pre) ” &&
  “ (l_pre <= r_pre) ” &&
  “ (r_pre <= 1000000000000000000) ” &&
  “ ((0 : Int) < x) ” &&
  “ (x <= 18446744073709551615) ” &&
  “ ((0 : Int) <= (b - 1)) ” &&
  “ ((b - 1) <= 63) ” &&
  “ (HighestBitScan l_pre r_pre x (b - 1)) ”
  &&  emp
) \/
(
forall (r_pre : Int) (l_pre : Int) (b : Int) (x : Int) (PreH1 : ((Z.land (Z.shiftr x b) 1) = (0 : Int))) (PreH2 : (1 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= 1000000000000000000)) (PreH5 : ((0 : Int) < x)) (PreH6 : (x <= 18446744073709551615)) (PreH7 : ((0 : Int) <= b)) (PreH8 : (b <= 63)) (PreH9 : (HighestBitScan l_pre r_pre x b)) ,
  TT && emp 
|--
  “ (HighestBitScan l_pre r_pre x (b - 1)) ” &&
  “ ((0 : Int) <= (b - 1)) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_split_goal_1 : Prop :=
  forall (r_pre : Int) (l_pre : Int) (b : Int) (x : Int) (PreH1 : ((Z.land (Z.shiftr x b) 1) = (0 : Int))) (PreH2 : (1 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= 1000000000000000000)) (PreH5 : ((0 : Int) < x)) (PreH6 : (x <= 18446744073709551615)) (PreH7 : ((0 : Int) <= b)) (PreH8 : (b <= 63)) (PreH9 : (HighestBitScan l_pre r_pre x b)) ,
  (HighestBitScan l_pre r_pre x (b - 1))

noncomputable def solver_entail_wit_2_split_goal_2 : Prop :=
  forall (r_pre : Int) (l_pre : Int) (b : Int) (x : Int) (PreH1 : ((Z.land (Z.shiftr x b) 1) = (0 : Int))) (PreH2 : (1 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= 1000000000000000000)) (PreH5 : ((0 : Int) < x)) (PreH6 : (x <= 18446744073709551615)) (PreH7 : ((0 : Int) <= b)) (PreH8 : (b <= 63)) (PreH9 : (HighestBitScan l_pre r_pre x b)) ,
  ((0 : Int) <= (b - 1))

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (r_pre : Int) (l_pre : Int) (b : Int) (x : Int) (PreH1 : (b = 63)) (PreH2 : ((Z.land (Z.shiftr x b) 1) ≠ (0 : Int))) (PreH3 : (1 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : (r_pre <= 1000000000000000000)) (PreH6 : ((0 : Int) < x)) (PreH7 : (x <= 18446744073709551615)) (PreH8 : ((0 : Int) <= b)) (PreH9 : (b <= 63)) (PreH10 : (HighestBitScan l_pre r_pre x b)) ,
  TT && emp 
|--
  “ (Spec l_pre r_pre (unsigned_last_nbits ((Z.lnot (0 : Int))) (64))) ”
  &&  emp
) \/
(
forall (r_pre : Int) (l_pre : Int) (b : Int) (x : Int) (PreH1 : (b = 63)) (PreH2 : ((Z.land (Z.shiftr x b) 1) ≠ (0 : Int))) (PreH3 : (1 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : (r_pre <= 1000000000000000000)) (PreH6 : ((0 : Int) < x)) (PreH7 : (x <= 18446744073709551615)) (PreH8 : ((0 : Int) <= b)) (PreH9 : (b <= 63)) (PreH10 : (HighestBitScan l_pre r_pre x b)) ,
  TT && emp 
|--
  “ (Spec l_pre r_pre (unsigned_last_nbits ((Z.lnot (0 : Int))) (64))) ”
  &&  emp
)

noncomputable def solver_return_wit_1_split_goal_1 : Prop :=
  forall (r_pre : Int) (l_pre : Int) (b : Int) (x : Int) (PreH1 : (b = 63)) (PreH2 : ((Z.land (Z.shiftr x b) 1) ≠ (0 : Int))) (PreH3 : (1 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : (r_pre <= 1000000000000000000)) (PreH6 : ((0 : Int) < x)) (PreH7 : (x <= 18446744073709551615)) (PreH8 : ((0 : Int) <= b)) (PreH9 : (b <= 63)) (PreH10 : (HighestBitScan l_pre r_pre x b)) ,
  (Spec l_pre r_pre (unsigned_last_nbits ((Z.lnot (0 : Int))) (64)))

noncomputable def solver_return_wit_2 : Prop :=
  (
forall (r_pre : Int) (l_pre : Int) (b : Int) (x : Int) (PreH1 : (b ≠ 63)) (PreH2 : ((Z.land (Z.shiftr x b) 1) ≠ (0 : Int))) (PreH3 : (1 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : (r_pre <= 1000000000000000000)) (PreH6 : ((0 : Int) < x)) (PreH7 : (x <= 18446744073709551615)) (PreH8 : ((0 : Int) <= b)) (PreH9 : (b <= 63)) (PreH10 : (HighestBitScan l_pre r_pre x b)) ,
  TT && emp 
|--
  “ (Spec l_pre r_pre (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl 1 (b + 1))) (64)) - 1)) (64))) ”
  &&  emp
) \/
(
forall (r_pre : Int) (l_pre : Int) (b : Int) (x : Int) (PreH1 : (b ≠ 63)) (PreH2 : ((Z.land (Z.shiftr x b) 1) ≠ (0 : Int))) (PreH3 : (1 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : (r_pre <= 1000000000000000000)) (PreH6 : ((0 : Int) < x)) (PreH7 : (x <= 18446744073709551615)) (PreH8 : ((0 : Int) <= b)) (PreH9 : (b <= 63)) (PreH10 : (HighestBitScan l_pre r_pre x b)) ,
  TT && emp 
|--
  “ (Spec l_pre r_pre (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl 1 (b + 1))) (64)) - 1)) (64))) ”
  &&  emp
)

noncomputable def solver_return_wit_2_split_goal_1 : Prop :=
  forall (r_pre : Int) (l_pre : Int) (b : Int) (x : Int) (PreH1 : (b ≠ 63)) (PreH2 : ((Z.land (Z.shiftr x b) 1) ≠ (0 : Int))) (PreH3 : (1 <= l_pre)) (PreH4 : (l_pre <= r_pre)) (PreH5 : (r_pre <= 1000000000000000000)) (PreH6 : ((0 : Int) < x)) (PreH7 : (x <= 18446744073709551615)) (PreH8 : ((0 : Int) <= b)) (PreH9 : (b <= 63)) (PreH10 : (HighestBitScan l_pre r_pre x b)) ,
  (Spec l_pre r_pre (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl 1 (b + 1))) (64)) - 1)) (64)))

noncomputable def solver_return_wit_3 : Prop :=
  (
forall (r_pre : Int) (l_pre : Int) (PreH1 : ((Z.lxor l_pre r_pre) = (0 : Int))) (PreH2 : (1 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= 1000000000000000000)) ,
  TT && emp 
|--
  “ (Spec l_pre r_pre (0 : Int)) ”
  &&  emp
) \/
(
forall (r_pre : Int) (l_pre : Int) (PreH1 : ((Z.lxor l_pre r_pre) = (0 : Int))) (PreH2 : (1 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= 1000000000000000000)) ,
  TT && emp 
|--
  “ (Spec l_pre r_pre (0 : Int)) ”
  &&  emp
)

noncomputable def solver_return_wit_3_split_goal_1 : Prop :=
  forall (r_pre : Int) (l_pre : Int) (PreH1 : ((Z.lxor l_pre r_pre) = (0 : Int))) (PreH2 : (1 <= l_pre)) (PreH3 : (l_pre <= r_pre)) (PreH4 : (r_pre <= 1000000000000000000)) ,
  (Spec l_pre r_pre (0 : Int))


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
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_2 : solver_entail_wit_2
  proof_of_solver_return_wit_1 : solver_return_wit_1
  proof_of_solver_return_wit_2 : solver_return_wit_2
  proof_of_solver_return_wit_3 : solver_return_wit_3

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P055_276D_little_girl_and_maximum_xor_goal
