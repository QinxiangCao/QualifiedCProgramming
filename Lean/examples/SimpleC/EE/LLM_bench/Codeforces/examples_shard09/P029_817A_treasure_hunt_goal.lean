import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P029_817A_treasure_hunt_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P029_817A_treasure_hunt_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P029_817A_treasure_hunt_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P029_817A_treasure_hunt_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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
  forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : (x1_pre >= x2_pre)) (PreH2 : ((-100000) <= x1_pre)) (PreH3 : (x1_pre <= 100000)) (PreH4 : ((-100000) <= y1_pre)) (PreH5 : (y1_pre <= 100000)) (PreH6 : ((-100000) <= x2_pre)) (PreH7 : (x2_pre <= 100000)) (PreH8 : ((-100000) <= y2_pre)) (PreH9 : (y2_pre <= 100000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= 100000)) (PreH12 : (1 <= y_pre)) (PreH13 : (y_pre <= 100000)) ,
  ((( &( "dy" ) )) # Int64 |->_)
  ** ((( &( "dx" ) )) # Int64 |->_)
  ** ((( &( "x1" ) )) # Int64 |-> (x1_pre))
  ** ((( &( "y1" ) )) # Int64 |-> (y1_pre))
  ** ((( &( "x2" ) )) # Int64 |-> (x2_pre))
  ** ((( &( "y2" ) )) # Int64 |-> (y2_pre))
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
|--
  “ ((x1_pre - x2_pre) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (x1_pre - x2_pre)) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : (x1_pre < x2_pre)) (PreH2 : ((-100000) <= x1_pre)) (PreH3 : (x1_pre <= 100000)) (PreH4 : ((-100000) <= y1_pre)) (PreH5 : (y1_pre <= 100000)) (PreH6 : ((-100000) <= x2_pre)) (PreH7 : (x2_pre <= 100000)) (PreH8 : ((-100000) <= y2_pre)) (PreH9 : (y2_pre <= 100000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= 100000)) (PreH12 : (1 <= y_pre)) (PreH13 : (y_pre <= 100000)) ,
  ((( &( "dy" ) )) # Int64 |->_)
  ** ((( &( "dx" ) )) # Int64 |->_)
  ** ((( &( "x1" ) )) # Int64 |-> (x1_pre))
  ** ((( &( "y1" ) )) # Int64 |-> (y1_pre))
  ** ((( &( "x2" ) )) # Int64 |-> (x2_pre))
  ** ((( &( "y2" ) )) # Int64 |-> (y2_pre))
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
|--
  “ ((x2_pre - x1_pre) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (x2_pre - x1_pre)) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : (y1_pre >= y2_pre)) (PreH2 : ((AbsDiff (x1_pre) (x2_pre)) = (AbsDiff (x1_pre) (x2_pre)))) (PreH3 : ((-100000) <= x1_pre)) (PreH4 : (x1_pre <= 100000)) (PreH5 : ((-100000) <= y1_pre)) (PreH6 : (y1_pre <= 100000)) (PreH7 : ((-100000) <= x2_pre)) (PreH8 : (x2_pre <= 100000)) (PreH9 : ((-100000) <= y2_pre)) (PreH10 : (y2_pre <= 100000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= 100000)) (PreH13 : (1 <= y_pre)) (PreH14 : (y_pre <= 100000)) ,
  ((( &( "dx" ) )) # Int64 |-> ((AbsDiff (x1_pre) (x2_pre))))
  ** ((( &( "x2" ) )) # Int64 |-> (x2_pre))
  ** ((( &( "x1" ) )) # Int64 |-> (x1_pre))
  ** ((( &( "dy" ) )) # Int64 |->_)
  ** ((( &( "y1" ) )) # Int64 |-> (y1_pre))
  ** ((( &( "y2" ) )) # Int64 |-> (y2_pre))
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
|--
  “ ((y1_pre - y2_pre) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (y1_pre - y2_pre)) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : (y1_pre < y2_pre)) (PreH2 : ((AbsDiff (x1_pre) (x2_pre)) = (AbsDiff (x1_pre) (x2_pre)))) (PreH3 : ((-100000) <= x1_pre)) (PreH4 : (x1_pre <= 100000)) (PreH5 : ((-100000) <= y1_pre)) (PreH6 : (y1_pre <= 100000)) (PreH7 : ((-100000) <= x2_pre)) (PreH8 : (x2_pre <= 100000)) (PreH9 : ((-100000) <= y2_pre)) (PreH10 : (y2_pre <= 100000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= 100000)) (PreH13 : (1 <= y_pre)) (PreH14 : (y_pre <= 100000)) ,
  ((( &( "dx" ) )) # Int64 |-> ((AbsDiff (x1_pre) (x2_pre))))
  ** ((( &( "x2" ) )) # Int64 |-> (x2_pre))
  ** ((( &( "x1" ) )) # Int64 |-> (x1_pre))
  ** ((( &( "dy" ) )) # Int64 |->_)
  ** ((( &( "y1" ) )) # Int64 |-> (y1_pre))
  ** ((( &( "y2" ) )) # Int64 |-> (y2_pre))
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
|--
  “ ((y2_pre - y1_pre) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (y2_pre - y1_pre)) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : ((AbsDiff (y1_pre) (y2_pre)) = (AbsDiff (y1_pre) (y2_pre)))) (PreH2 : ((-100000) <= x1_pre)) (PreH3 : (x1_pre <= 100000)) (PreH4 : ((-100000) <= y1_pre)) (PreH5 : (y1_pre <= 100000)) (PreH6 : ((-100000) <= x2_pre)) (PreH7 : (x2_pre <= 100000)) (PreH8 : ((-100000) <= y2_pre)) (PreH9 : (y2_pre <= 100000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= 100000)) (PreH12 : (1 <= y_pre)) (PreH13 : (y_pre <= 100000)) ,
  ((( &( "dy" ) )) # Int64 |-> ((AbsDiff (y1_pre) (y2_pre))))
  ** ((( &( "y2" ) )) # Int64 |-> (y2_pre))
  ** ((( &( "y1" ) )) # Int64 |-> (y1_pre))
  ** ((( &( "dx" ) )) # Int64 |-> ((AbsDiff (x1_pre) (x2_pre))))
  ** ((( &( "x2" ) )) # Int64 |-> (x2_pre))
  ** ((( &( "x1" ) )) # Int64 |-> (x1_pre))
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
|--
  “ (((AbsDiff (x1_pre) (x2_pre)) ≠ (-9223372036854775808)) ∨ (x_pre ≠ (-1))) ” &&
  “ (x_pre ≠ (0 : Int)) ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : ((AbsDiff (y1_pre) (y2_pre)) = (AbsDiff (y1_pre) (y2_pre)))) (PreH2 : ((-100000) <= x1_pre)) (PreH3 : (x1_pre <= 100000)) (PreH4 : ((-100000) <= y1_pre)) (PreH5 : (y1_pre <= 100000)) (PreH6 : ((-100000) <= x2_pre)) (PreH7 : (x2_pre <= 100000)) (PreH8 : ((-100000) <= y2_pre)) (PreH9 : (y2_pre <= 100000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= 100000)) (PreH12 : (1 <= y_pre)) (PreH13 : (y_pre <= 100000)) ,
  ((( &( "dy" ) )) # Int64 |-> ((AbsDiff (y1_pre) (y2_pre))))
  ** ((( &( "y2" ) )) # Int64 |-> (y2_pre))
  ** ((( &( "y1" ) )) # Int64 |-> (y1_pre))
  ** ((( &( "dx" ) )) # Int64 |-> ((AbsDiff (x1_pre) (x2_pre))))
  ** ((( &( "x2" ) )) # Int64 |-> (x2_pre))
  ** ((( &( "x1" ) )) # Int64 |-> (x1_pre))
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_7 : Prop :=
  forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : ((Z.rem (AbsDiff (x1_pre) (x2_pre)) x_pre) = (0 : Int))) (PreH2 : ((AbsDiff (y1_pre) (y2_pre)) = (AbsDiff (y1_pre) (y2_pre)))) (PreH3 : ((-100000) <= x1_pre)) (PreH4 : (x1_pre <= 100000)) (PreH5 : ((-100000) <= y1_pre)) (PreH6 : (y1_pre <= 100000)) (PreH7 : ((-100000) <= x2_pre)) (PreH8 : (x2_pre <= 100000)) (PreH9 : ((-100000) <= y2_pre)) (PreH10 : (y2_pre <= 100000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= 100000)) (PreH13 : (1 <= y_pre)) (PreH14 : (y_pre <= 100000)) ,
  ((( &( "dy" ) )) # Int64 |-> ((AbsDiff (y1_pre) (y2_pre))))
  ** ((( &( "y2" ) )) # Int64 |-> (y2_pre))
  ** ((( &( "y1" ) )) # Int64 |-> (y1_pre))
  ** ((( &( "dx" ) )) # Int64 |-> ((AbsDiff (x1_pre) (x2_pre))))
  ** ((( &( "x2" ) )) # Int64 |-> (x2_pre))
  ** ((( &( "x1" ) )) # Int64 |-> (x1_pre))
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
|--
  “ (((AbsDiff (y1_pre) (y2_pre)) ≠ (-9223372036854775808)) ∨ (y_pre ≠ (-1))) ” &&
  “ (y_pre ≠ (0 : Int)) ”

noncomputable def solver_safety_wit_8 : Prop :=
  forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : ((Z.rem (AbsDiff (x1_pre) (x2_pre)) x_pre) = (0 : Int))) (PreH2 : ((AbsDiff (y1_pre) (y2_pre)) = (AbsDiff (y1_pre) (y2_pre)))) (PreH3 : ((-100000) <= x1_pre)) (PreH4 : (x1_pre <= 100000)) (PreH5 : ((-100000) <= y1_pre)) (PreH6 : (y1_pre <= 100000)) (PreH7 : ((-100000) <= x2_pre)) (PreH8 : (x2_pre <= 100000)) (PreH9 : ((-100000) <= y2_pre)) (PreH10 : (y2_pre <= 100000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= 100000)) (PreH13 : (1 <= y_pre)) (PreH14 : (y_pre <= 100000)) ,
  ((( &( "dy" ) )) # Int64 |-> ((AbsDiff (y1_pre) (y2_pre))))
  ** ((( &( "y2" ) )) # Int64 |-> (y2_pre))
  ** ((( &( "y1" ) )) # Int64 |-> (y1_pre))
  ** ((( &( "dx" ) )) # Int64 |-> ((AbsDiff (x1_pre) (x2_pre))))
  ** ((( &( "x2" ) )) # Int64 |-> (x2_pre))
  ** ((( &( "x1" ) )) # Int64 |-> (x1_pre))
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_9 : Prop :=
  forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : ((Z.rem (AbsDiff (x1_pre) (x2_pre)) x_pre) ≠ (0 : Int))) (PreH2 : ((AbsDiff (y1_pre) (y2_pre)) = (AbsDiff (y1_pre) (y2_pre)))) (PreH3 : ((-100000) <= x1_pre)) (PreH4 : (x1_pre <= 100000)) (PreH5 : ((-100000) <= y1_pre)) (PreH6 : (y1_pre <= 100000)) (PreH7 : ((-100000) <= x2_pre)) (PreH8 : (x2_pre <= 100000)) (PreH9 : ((-100000) <= y2_pre)) (PreH10 : (y2_pre <= 100000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= 100000)) (PreH13 : (1 <= y_pre)) (PreH14 : (y_pre <= 100000)) ,
  ((( &( "dy" ) )) # Int64 |-> ((AbsDiff (y1_pre) (y2_pre))))
  ** ((( &( "y2" ) )) # Int64 |-> (y2_pre))
  ** ((( &( "y1" ) )) # Int64 |-> (y1_pre))
  ** ((( &( "dx" ) )) # Int64 |-> ((AbsDiff (x1_pre) (x2_pre))))
  ** ((( &( "x2" ) )) # Int64 |-> (x2_pre))
  ** ((( &( "x1" ) )) # Int64 |-> (x1_pre))
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_10 : Prop :=
  forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : ((Z.rem (AbsDiff (y1_pre) (y2_pre)) y_pre) ≠ (0 : Int))) (PreH2 : ((Z.rem (AbsDiff (x1_pre) (x2_pre)) x_pre) = (0 : Int))) (PreH3 : ((AbsDiff (y1_pre) (y2_pre)) = (AbsDiff (y1_pre) (y2_pre)))) (PreH4 : ((-100000) <= x1_pre)) (PreH5 : (x1_pre <= 100000)) (PreH6 : ((-100000) <= y1_pre)) (PreH7 : (y1_pre <= 100000)) (PreH8 : ((-100000) <= x2_pre)) (PreH9 : (x2_pre <= 100000)) (PreH10 : ((-100000) <= y2_pre)) (PreH11 : (y2_pre <= 100000)) (PreH12 : (1 <= x_pre)) (PreH13 : (x_pre <= 100000)) (PreH14 : (1 <= y_pre)) (PreH15 : (y_pre <= 100000)) ,
  ((( &( "dy" ) )) # Int64 |-> ((AbsDiff (y1_pre) (y2_pre))))
  ** ((( &( "y2" ) )) # Int64 |-> (y2_pre))
  ** ((( &( "y1" ) )) # Int64 |-> (y1_pre))
  ** ((( &( "dx" ) )) # Int64 |-> ((AbsDiff (x1_pre) (x2_pre))))
  ** ((( &( "x2" ) )) # Int64 |-> (x2_pre))
  ** ((( &( "x1" ) )) # Int64 |-> (x1_pre))
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_11 : Prop :=
  forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : ((Z.rem (AbsDiff (y1_pre) (y2_pre)) y_pre) = (0 : Int))) (PreH2 : ((Z.rem (AbsDiff (x1_pre) (x2_pre)) x_pre) = (0 : Int))) (PreH3 : ((AbsDiff (y1_pre) (y2_pre)) = (AbsDiff (y1_pre) (y2_pre)))) (PreH4 : ((-100000) <= x1_pre)) (PreH5 : (x1_pre <= 100000)) (PreH6 : ((-100000) <= y1_pre)) (PreH7 : (y1_pre <= 100000)) (PreH8 : ((-100000) <= x2_pre)) (PreH9 : (x2_pre <= 100000)) (PreH10 : ((-100000) <= y2_pre)) (PreH11 : (y2_pre <= 100000)) (PreH12 : (1 <= x_pre)) (PreH13 : (x_pre <= 100000)) (PreH14 : (1 <= y_pre)) (PreH15 : (y_pre <= 100000)) ,
  ((( &( "dy" ) )) # Int64 |-> ((AbsDiff (y1_pre) (y2_pre))))
  ** ((( &( "y2" ) )) # Int64 |-> (y2_pre))
  ** ((( &( "y1" ) )) # Int64 |-> (y1_pre))
  ** ((( &( "dx" ) )) # Int64 |-> ((AbsDiff (x1_pre) (x2_pre))))
  ** ((( &( "x2" ) )) # Int64 |-> (x2_pre))
  ** ((( &( "x1" ) )) # Int64 |-> (x1_pre))
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
|--
  “ (((Z.quot (AbsDiff (y1_pre) (y2_pre)) y_pre) ≠ (-9223372036854775808)) ∨ (2 ≠ (-1))) ” &&
  “ (2 ≠ (0 : Int)) ”

noncomputable def solver_safety_wit_12 : Prop :=
  forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : ((Z.rem (AbsDiff (y1_pre) (y2_pre)) y_pre) = (0 : Int))) (PreH2 : ((Z.rem (AbsDiff (x1_pre) (x2_pre)) x_pre) = (0 : Int))) (PreH3 : ((AbsDiff (y1_pre) (y2_pre)) = (AbsDiff (y1_pre) (y2_pre)))) (PreH4 : ((-100000) <= x1_pre)) (PreH5 : (x1_pre <= 100000)) (PreH6 : ((-100000) <= y1_pre)) (PreH7 : (y1_pre <= 100000)) (PreH8 : ((-100000) <= x2_pre)) (PreH9 : (x2_pre <= 100000)) (PreH10 : ((-100000) <= y2_pre)) (PreH11 : (y2_pre <= 100000)) (PreH12 : (1 <= x_pre)) (PreH13 : (x_pre <= 100000)) (PreH14 : (1 <= y_pre)) (PreH15 : (y_pre <= 100000)) ,
  ((( &( "dy" ) )) # Int64 |-> ((AbsDiff (y1_pre) (y2_pre))))
  ** ((( &( "y2" ) )) # Int64 |-> (y2_pre))
  ** ((( &( "y1" ) )) # Int64 |-> (y1_pre))
  ** ((( &( "dx" ) )) # Int64 |-> ((AbsDiff (x1_pre) (x2_pre))))
  ** ((( &( "x2" ) )) # Int64 |-> (x2_pre))
  ** ((( &( "x1" ) )) # Int64 |-> (x1_pre))
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
|--
  “ (((AbsDiff (y1_pre) (y2_pre)) ≠ (-9223372036854775808)) ∨ (y_pre ≠ (-1))) ” &&
  “ (y_pre ≠ (0 : Int)) ”

noncomputable def solver_safety_wit_13 : Prop :=
  forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : ((Z.rem (AbsDiff (y1_pre) (y2_pre)) y_pre) = (0 : Int))) (PreH2 : ((Z.rem (AbsDiff (x1_pre) (x2_pre)) x_pre) = (0 : Int))) (PreH3 : ((AbsDiff (y1_pre) (y2_pre)) = (AbsDiff (y1_pre) (y2_pre)))) (PreH4 : ((-100000) <= x1_pre)) (PreH5 : (x1_pre <= 100000)) (PreH6 : ((-100000) <= y1_pre)) (PreH7 : (y1_pre <= 100000)) (PreH8 : ((-100000) <= x2_pre)) (PreH9 : (x2_pre <= 100000)) (PreH10 : ((-100000) <= y2_pre)) (PreH11 : (y2_pre <= 100000)) (PreH12 : (1 <= x_pre)) (PreH13 : (x_pre <= 100000)) (PreH14 : (1 <= y_pre)) (PreH15 : (y_pre <= 100000)) ,
  ((( &( "dy" ) )) # Int64 |-> ((AbsDiff (y1_pre) (y2_pre))))
  ** ((( &( "y2" ) )) # Int64 |-> (y2_pre))
  ** ((( &( "y1" ) )) # Int64 |-> (y1_pre))
  ** ((( &( "dx" ) )) # Int64 |-> ((AbsDiff (x1_pre) (x2_pre))))
  ** ((( &( "x2" ) )) # Int64 |-> (x2_pre))
  ** ((( &( "x1" ) )) # Int64 |-> (x1_pre))
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
|--
  “ (((Z.quot (AbsDiff (x1_pre) (x2_pre)) x_pre) ≠ (-9223372036854775808)) ∨ (2 ≠ (-1))) ” &&
  “ (2 ≠ (0 : Int)) ”

noncomputable def solver_safety_wit_14 : Prop :=
  forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : ((Z.rem (AbsDiff (y1_pre) (y2_pre)) y_pre) = (0 : Int))) (PreH2 : ((Z.rem (AbsDiff (x1_pre) (x2_pre)) x_pre) = (0 : Int))) (PreH3 : ((AbsDiff (y1_pre) (y2_pre)) = (AbsDiff (y1_pre) (y2_pre)))) (PreH4 : ((-100000) <= x1_pre)) (PreH5 : (x1_pre <= 100000)) (PreH6 : ((-100000) <= y1_pre)) (PreH7 : (y1_pre <= 100000)) (PreH8 : ((-100000) <= x2_pre)) (PreH9 : (x2_pre <= 100000)) (PreH10 : ((-100000) <= y2_pre)) (PreH11 : (y2_pre <= 100000)) (PreH12 : (1 <= x_pre)) (PreH13 : (x_pre <= 100000)) (PreH14 : (1 <= y_pre)) (PreH15 : (y_pre <= 100000)) ,
  ((( &( "dy" ) )) # Int64 |-> ((AbsDiff (y1_pre) (y2_pre))))
  ** ((( &( "y2" ) )) # Int64 |-> (y2_pre))
  ** ((( &( "y1" ) )) # Int64 |-> (y1_pre))
  ** ((( &( "dx" ) )) # Int64 |-> ((AbsDiff (x1_pre) (x2_pre))))
  ** ((( &( "x2" ) )) # Int64 |-> (x2_pre))
  ** ((( &( "x1" ) )) # Int64 |-> (x1_pre))
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
|--
  “ (((AbsDiff (x1_pre) (x2_pre)) ≠ (-9223372036854775808)) ∨ (x_pre ≠ (-1))) ” &&
  “ (x_pre ≠ (0 : Int)) ”

noncomputable def solver_safety_wit_15 : Prop :=
  forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : ((Z.rem (AbsDiff (y1_pre) (y2_pre)) y_pre) = (0 : Int))) (PreH2 : ((Z.rem (AbsDiff (x1_pre) (x2_pre)) x_pre) = (0 : Int))) (PreH3 : ((AbsDiff (y1_pre) (y2_pre)) = (AbsDiff (y1_pre) (y2_pre)))) (PreH4 : ((-100000) <= x1_pre)) (PreH5 : (x1_pre <= 100000)) (PreH6 : ((-100000) <= y1_pre)) (PreH7 : (y1_pre <= 100000)) (PreH8 : ((-100000) <= x2_pre)) (PreH9 : (x2_pre <= 100000)) (PreH10 : ((-100000) <= y2_pre)) (PreH11 : (y2_pre <= 100000)) (PreH12 : (1 <= x_pre)) (PreH13 : (x_pre <= 100000)) (PreH14 : (1 <= y_pre)) (PreH15 : (y_pre <= 100000)) ,
  ((( &( "dy" ) )) # Int64 |-> ((AbsDiff (y1_pre) (y2_pre))))
  ** ((( &( "y2" ) )) # Int64 |-> (y2_pre))
  ** ((( &( "y1" ) )) # Int64 |-> (y1_pre))
  ** ((( &( "dx" ) )) # Int64 |-> ((AbsDiff (x1_pre) (x2_pre))))
  ** ((( &( "x2" ) )) # Int64 |-> (x2_pre))
  ** ((( &( "x1" ) )) # Int64 |-> (x1_pre))
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_16 : Prop :=
  forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : ((Z.rem (AbsDiff (y1_pre) (y2_pre)) y_pre) = (0 : Int))) (PreH2 : ((Z.rem (AbsDiff (x1_pre) (x2_pre)) x_pre) = (0 : Int))) (PreH3 : ((AbsDiff (y1_pre) (y2_pre)) = (AbsDiff (y1_pre) (y2_pre)))) (PreH4 : ((-100000) <= x1_pre)) (PreH5 : (x1_pre <= 100000)) (PreH6 : ((-100000) <= y1_pre)) (PreH7 : (y1_pre <= 100000)) (PreH8 : ((-100000) <= x2_pre)) (PreH9 : (x2_pre <= 100000)) (PreH10 : ((-100000) <= y2_pre)) (PreH11 : (y2_pre <= 100000)) (PreH12 : (1 <= x_pre)) (PreH13 : (x_pre <= 100000)) (PreH14 : (1 <= y_pre)) (PreH15 : (y_pre <= 100000)) ,
  ((( &( "dy" ) )) # Int64 |-> ((AbsDiff (y1_pre) (y2_pre))))
  ** ((( &( "y2" ) )) # Int64 |-> (y2_pre))
  ** ((( &( "y1" ) )) # Int64 |-> (y1_pre))
  ** ((( &( "dx" ) )) # Int64 |-> ((AbsDiff (x1_pre) (x2_pre))))
  ** ((( &( "x2" ) )) # Int64 |-> (x2_pre))
  ** ((( &( "x1" ) )) # Int64 |-> (x1_pre))
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_entail_wit_1_1 : Prop :=
  (
forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : (x1_pre >= x2_pre)) (PreH2 : ((-100000) <= x1_pre)) (PreH3 : (x1_pre <= 100000)) (PreH4 : ((-100000) <= y1_pre)) (PreH5 : (y1_pre <= 100000)) (PreH6 : ((-100000) <= x2_pre)) (PreH7 : (x2_pre <= 100000)) (PreH8 : ((-100000) <= y2_pre)) (PreH9 : (y2_pre <= 100000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= 100000)) (PreH12 : (1 <= y_pre)) (PreH13 : (y_pre <= 100000)) ,
  ((( &( "dy" ) )) # Int64 |->_)
  ** ((( &( "dx" ) )) # Int64 |-> ((x1_pre - x2_pre)))
|--
  “ ((AbsDiff (x1_pre) (x2_pre)) = (AbsDiff (x1_pre) (x2_pre))) ” &&
  “ ((-100000) <= x1_pre) ” &&
  “ (x1_pre <= 100000) ” &&
  “ ((-100000) <= y1_pre) ” &&
  “ (y1_pre <= 100000) ” &&
  “ ((-100000) <= x2_pre) ” &&
  “ (x2_pre <= 100000) ” &&
  “ ((-100000) <= y2_pre) ” &&
  “ (y2_pre <= 100000) ” &&
  “ (1 <= x_pre) ” &&
  “ (x_pre <= 100000) ” &&
  “ (1 <= y_pre) ” &&
  “ (y_pre <= 100000) ”
  &&  ((( &( "dx" ) )) # Int64 |-> ((AbsDiff (x1_pre) (x2_pre))))
  ** ((( &( "dy" ) )) # Int64 |->_)
) \/
(
forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : (x1_pre >= x2_pre)) (PreH2 : ((-100000) <= x1_pre)) (PreH3 : (x1_pre <= 100000)) (PreH4 : ((-100000) <= y1_pre)) (PreH5 : (y1_pre <= 100000)) (PreH6 : ((-100000) <= x2_pre)) (PreH7 : (x2_pre <= 100000)) (PreH8 : ((-100000) <= y2_pre)) (PreH9 : (y2_pre <= 100000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= 100000)) (PreH12 : (1 <= y_pre)) (PreH13 : (y_pre <= 100000)) ,
  ((( &( "dy" ) )) # Int64 |->_)
|--
  EX x : Int,
  “ ((x1_pre - x2_pre) = (AbsDiff (x1_pre) (x2_pre))) ” &&
  “ ((-100000) <= x1_pre) ” &&
  “ (x1_pre <= 100000) ” &&
  “ ((-100000) <= y1_pre) ” &&
  “ (y1_pre <= 100000) ” &&
  “ ((-100000) <= x2_pre) ” &&
  “ (x2_pre <= 100000) ” &&
  “ ((-100000) <= y2_pre) ” &&
  “ (y2_pre <= 100000) ” &&
  “ (1 <= x_pre) ” &&
  “ (x_pre <= 100000) ” &&
  “ (1 <= y_pre) ” &&
  “ (y_pre <= 100000) ”
  &&  ((( &( "dy" ) )) # Int64 |-> (x))
)

noncomputable def solver_entail_wit_1_2 : Prop :=
  (
forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : (x1_pre < x2_pre)) (PreH2 : ((-100000) <= x1_pre)) (PreH3 : (x1_pre <= 100000)) (PreH4 : ((-100000) <= y1_pre)) (PreH5 : (y1_pre <= 100000)) (PreH6 : ((-100000) <= x2_pre)) (PreH7 : (x2_pre <= 100000)) (PreH8 : ((-100000) <= y2_pre)) (PreH9 : (y2_pre <= 100000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= 100000)) (PreH12 : (1 <= y_pre)) (PreH13 : (y_pre <= 100000)) ,
  ((( &( "dy" ) )) # Int64 |->_)
  ** ((( &( "dx" ) )) # Int64 |-> ((x2_pre - x1_pre)))
|--
  “ ((AbsDiff (x1_pre) (x2_pre)) = (AbsDiff (x1_pre) (x2_pre))) ” &&
  “ ((-100000) <= x1_pre) ” &&
  “ (x1_pre <= 100000) ” &&
  “ ((-100000) <= y1_pre) ” &&
  “ (y1_pre <= 100000) ” &&
  “ ((-100000) <= x2_pre) ” &&
  “ (x2_pre <= 100000) ” &&
  “ ((-100000) <= y2_pre) ” &&
  “ (y2_pre <= 100000) ” &&
  “ (1 <= x_pre) ” &&
  “ (x_pre <= 100000) ” &&
  “ (1 <= y_pre) ” &&
  “ (y_pre <= 100000) ”
  &&  ((( &( "dx" ) )) # Int64 |-> ((AbsDiff (x1_pre) (x2_pre))))
  ** ((( &( "dy" ) )) # Int64 |->_)
) \/
(
forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : (x1_pre < x2_pre)) (PreH2 : ((-100000) <= x1_pre)) (PreH3 : (x1_pre <= 100000)) (PreH4 : ((-100000) <= y1_pre)) (PreH5 : (y1_pre <= 100000)) (PreH6 : ((-100000) <= x2_pre)) (PreH7 : (x2_pre <= 100000)) (PreH8 : ((-100000) <= y2_pre)) (PreH9 : (y2_pre <= 100000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= 100000)) (PreH12 : (1 <= y_pre)) (PreH13 : (y_pre <= 100000)) ,
  ((( &( "dy" ) )) # Int64 |->_)
|--
  EX x : Int,
  “ ((x2_pre - x1_pre) = (AbsDiff (x1_pre) (x2_pre))) ” &&
  “ ((-100000) <= x1_pre) ” &&
  “ (x1_pre <= 100000) ” &&
  “ ((-100000) <= y1_pre) ” &&
  “ (y1_pre <= 100000) ” &&
  “ ((-100000) <= x2_pre) ” &&
  “ (x2_pre <= 100000) ” &&
  “ ((-100000) <= y2_pre) ” &&
  “ (y2_pre <= 100000) ” &&
  “ (1 <= x_pre) ” &&
  “ (x_pre <= 100000) ” &&
  “ (1 <= y_pre) ” &&
  “ (y_pre <= 100000) ”
  &&  ((( &( "dy" ) )) # Int64 |-> (x))
)

noncomputable def solver_entail_wit_2_1 : Prop :=
  (
forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : (y1_pre >= y2_pre)) (PreH2 : ((AbsDiff (x1_pre) (x2_pre)) = (AbsDiff (x1_pre) (x2_pre)))) (PreH3 : ((-100000) <= x1_pre)) (PreH4 : (x1_pre <= 100000)) (PreH5 : ((-100000) <= y1_pre)) (PreH6 : (y1_pre <= 100000)) (PreH7 : ((-100000) <= x2_pre)) (PreH8 : (x2_pre <= 100000)) (PreH9 : ((-100000) <= y2_pre)) (PreH10 : (y2_pre <= 100000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= 100000)) (PreH13 : (1 <= y_pre)) (PreH14 : (y_pre <= 100000)) ,
  ((( &( "dy" ) )) # Int64 |-> ((y1_pre - y2_pre)))
|--
  “ ((AbsDiff (y1_pre) (y2_pre)) = (AbsDiff (y1_pre) (y2_pre))) ” &&
  “ ((-100000) <= x1_pre) ” &&
  “ (x1_pre <= 100000) ” &&
  “ ((-100000) <= y1_pre) ” &&
  “ (y1_pre <= 100000) ” &&
  “ ((-100000) <= x2_pre) ” &&
  “ (x2_pre <= 100000) ” &&
  “ ((-100000) <= y2_pre) ” &&
  “ (y2_pre <= 100000) ” &&
  “ (1 <= x_pre) ” &&
  “ (x_pre <= 100000) ” &&
  “ (1 <= y_pre) ” &&
  “ (y_pre <= 100000) ”
  &&  ((( &( "dy" ) )) # Int64 |-> ((AbsDiff (y1_pre) (y2_pre))))
) \/
(
forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : (y1_pre >= y2_pre)) (PreH2 : ((-100000) <= x1_pre)) (PreH3 : (x1_pre <= 100000)) (PreH4 : ((-100000) <= y1_pre)) (PreH5 : (y1_pre <= 100000)) (PreH6 : ((-100000) <= x2_pre)) (PreH7 : (x2_pre <= 100000)) (PreH8 : ((-100000) <= y2_pre)) (PreH9 : (y2_pre <= 100000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= 100000)) (PreH12 : (1 <= y_pre)) (PreH13 : (y_pre <= 100000)) ,
  TT && emp 
|--
  “ ((y1_pre - y2_pre) = (AbsDiff (y1_pre) (y2_pre))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_1_split_goal_1 : Prop :=
  forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : (y1_pre >= y2_pre)) (PreH2 : ((-100000) <= x1_pre)) (PreH3 : (x1_pre <= 100000)) (PreH4 : ((-100000) <= y1_pre)) (PreH5 : (y1_pre <= 100000)) (PreH6 : ((-100000) <= x2_pre)) (PreH7 : (x2_pre <= 100000)) (PreH8 : ((-100000) <= y2_pre)) (PreH9 : (y2_pre <= 100000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= 100000)) (PreH12 : (1 <= y_pre)) (PreH13 : (y_pre <= 100000)) ,
  ((y1_pre - y2_pre) = (AbsDiff (y1_pre) (y2_pre)))

noncomputable def solver_entail_wit_2_2 : Prop :=
  (
forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : (y1_pre < y2_pre)) (PreH2 : ((AbsDiff (x1_pre) (x2_pre)) = (AbsDiff (x1_pre) (x2_pre)))) (PreH3 : ((-100000) <= x1_pre)) (PreH4 : (x1_pre <= 100000)) (PreH5 : ((-100000) <= y1_pre)) (PreH6 : (y1_pre <= 100000)) (PreH7 : ((-100000) <= x2_pre)) (PreH8 : (x2_pre <= 100000)) (PreH9 : ((-100000) <= y2_pre)) (PreH10 : (y2_pre <= 100000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= 100000)) (PreH13 : (1 <= y_pre)) (PreH14 : (y_pre <= 100000)) ,
  ((( &( "dy" ) )) # Int64 |-> ((y2_pre - y1_pre)))
|--
  “ ((AbsDiff (y1_pre) (y2_pre)) = (AbsDiff (y1_pre) (y2_pre))) ” &&
  “ ((-100000) <= x1_pre) ” &&
  “ (x1_pre <= 100000) ” &&
  “ ((-100000) <= y1_pre) ” &&
  “ (y1_pre <= 100000) ” &&
  “ ((-100000) <= x2_pre) ” &&
  “ (x2_pre <= 100000) ” &&
  “ ((-100000) <= y2_pre) ” &&
  “ (y2_pre <= 100000) ” &&
  “ (1 <= x_pre) ” &&
  “ (x_pre <= 100000) ” &&
  “ (1 <= y_pre) ” &&
  “ (y_pre <= 100000) ”
  &&  ((( &( "dy" ) )) # Int64 |-> ((AbsDiff (y1_pre) (y2_pre))))
) \/
(
forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : (y1_pre < y2_pre)) (PreH2 : ((-100000) <= x1_pre)) (PreH3 : (x1_pre <= 100000)) (PreH4 : ((-100000) <= y1_pre)) (PreH5 : (y1_pre <= 100000)) (PreH6 : ((-100000) <= x2_pre)) (PreH7 : (x2_pre <= 100000)) (PreH8 : ((-100000) <= y2_pre)) (PreH9 : (y2_pre <= 100000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= 100000)) (PreH12 : (1 <= y_pre)) (PreH13 : (y_pre <= 100000)) ,
  TT && emp 
|--
  “ ((y2_pre - y1_pre) = (AbsDiff (y1_pre) (y2_pre))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_2_split_goal_1 : Prop :=
  forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : (y1_pre < y2_pre)) (PreH2 : ((-100000) <= x1_pre)) (PreH3 : (x1_pre <= 100000)) (PreH4 : ((-100000) <= y1_pre)) (PreH5 : (y1_pre <= 100000)) (PreH6 : ((-100000) <= x2_pre)) (PreH7 : (x2_pre <= 100000)) (PreH8 : ((-100000) <= y2_pre)) (PreH9 : (y2_pre <= 100000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= 100000)) (PreH12 : (1 <= y_pre)) (PreH13 : (y_pre <= 100000)) ,
  ((y2_pre - y1_pre) = (AbsDiff (y1_pre) (y2_pre)))

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : ((Z.rem (Z.quot (AbsDiff (x1_pre) (x2_pre)) x_pre) 2) ≠ (Z.rem (Z.quot (AbsDiff (y1_pre) (y2_pre)) y_pre) 2))) (PreH2 : ((Z.rem (AbsDiff (y1_pre) (y2_pre)) y_pre) = (0 : Int))) (PreH3 : ((Z.rem (AbsDiff (x1_pre) (x2_pre)) x_pre) = (0 : Int))) (PreH4 : ((AbsDiff (y1_pre) (y2_pre)) = (AbsDiff (y1_pre) (y2_pre)))) (PreH5 : ((-100000) <= x1_pre)) (PreH6 : (x1_pre <= 100000)) (PreH7 : ((-100000) <= y1_pre)) (PreH8 : (y1_pre <= 100000)) (PreH9 : ((-100000) <= x2_pre)) (PreH10 : (x2_pre <= 100000)) (PreH11 : ((-100000) <= y2_pre)) (PreH12 : (y2_pre <= 100000)) (PreH13 : (1 <= x_pre)) (PreH14 : (x_pre <= 100000)) (PreH15 : (1 <= y_pre)) (PreH16 : (y_pre <= 100000)) ,
  TT && emp 
|--
  “ (Spec x1_pre y1_pre x2_pre y2_pre x_pre y_pre (0 : Int)) ”
  &&  emp
) \/
(
forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : ((Z.rem (Z.quot (AbsDiff (x1_pre) (x2_pre)) x_pre) 2) ≠ (Z.rem (Z.quot (AbsDiff (y1_pre) (y2_pre)) y_pre) 2))) (PreH2 : ((Z.rem (AbsDiff (y1_pre) (y2_pre)) y_pre) = (0 : Int))) (PreH3 : ((Z.rem (AbsDiff (x1_pre) (x2_pre)) x_pre) = (0 : Int))) (PreH4 : ((-100000) <= x1_pre)) (PreH5 : (x1_pre <= 100000)) (PreH6 : ((-100000) <= y1_pre)) (PreH7 : (y1_pre <= 100000)) (PreH8 : ((-100000) <= x2_pre)) (PreH9 : (x2_pre <= 100000)) (PreH10 : ((-100000) <= y2_pre)) (PreH11 : (y2_pre <= 100000)) (PreH12 : (1 <= x_pre)) (PreH13 : (x_pre <= 100000)) (PreH14 : (1 <= y_pre)) (PreH15 : (y_pre <= 100000)) ,
  TT && emp 
|--
  “ (Spec x1_pre y1_pre x2_pre y2_pre x_pre y_pre (0 : Int)) ”
  &&  emp
)

noncomputable def solver_return_wit_1_split_goal_1 : Prop :=
  forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : ((Z.rem (Z.quot (AbsDiff (x1_pre) (x2_pre)) x_pre) 2) ≠ (Z.rem (Z.quot (AbsDiff (y1_pre) (y2_pre)) y_pre) 2))) (PreH2 : ((Z.rem (AbsDiff (y1_pre) (y2_pre)) y_pre) = (0 : Int))) (PreH3 : ((Z.rem (AbsDiff (x1_pre) (x2_pre)) x_pre) = (0 : Int))) (PreH4 : ((-100000) <= x1_pre)) (PreH5 : (x1_pre <= 100000)) (PreH6 : ((-100000) <= y1_pre)) (PreH7 : (y1_pre <= 100000)) (PreH8 : ((-100000) <= x2_pre)) (PreH9 : (x2_pre <= 100000)) (PreH10 : ((-100000) <= y2_pre)) (PreH11 : (y2_pre <= 100000)) (PreH12 : (1 <= x_pre)) (PreH13 : (x_pre <= 100000)) (PreH14 : (1 <= y_pre)) (PreH15 : (y_pre <= 100000)) ,
  (Spec x1_pre y1_pre x2_pre y2_pre x_pre y_pre (0 : Int))

noncomputable def solver_return_wit_2 : Prop :=
  (
forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : ((Z.rem (Z.quot (AbsDiff (x1_pre) (x2_pre)) x_pre) 2) = (Z.rem (Z.quot (AbsDiff (y1_pre) (y2_pre)) y_pre) 2))) (PreH2 : ((Z.rem (AbsDiff (y1_pre) (y2_pre)) y_pre) = (0 : Int))) (PreH3 : ((Z.rem (AbsDiff (x1_pre) (x2_pre)) x_pre) = (0 : Int))) (PreH4 : ((AbsDiff (y1_pre) (y2_pre)) = (AbsDiff (y1_pre) (y2_pre)))) (PreH5 : ((-100000) <= x1_pre)) (PreH6 : (x1_pre <= 100000)) (PreH7 : ((-100000) <= y1_pre)) (PreH8 : (y1_pre <= 100000)) (PreH9 : ((-100000) <= x2_pre)) (PreH10 : (x2_pre <= 100000)) (PreH11 : ((-100000) <= y2_pre)) (PreH12 : (y2_pre <= 100000)) (PreH13 : (1 <= x_pre)) (PreH14 : (x_pre <= 100000)) (PreH15 : (1 <= y_pre)) (PreH16 : (y_pre <= 100000)) ,
  TT && emp 
|--
  “ (Spec x1_pre y1_pre x2_pre y2_pre x_pre y_pre 1) ”
  &&  emp
) \/
(
forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : ((Z.rem (Z.quot (AbsDiff (x1_pre) (x2_pre)) x_pre) 2) = (Z.rem (Z.quot (AbsDiff (y1_pre) (y2_pre)) y_pre) 2))) (PreH2 : ((Z.rem (AbsDiff (y1_pre) (y2_pre)) y_pre) = (0 : Int))) (PreH3 : ((Z.rem (AbsDiff (x1_pre) (x2_pre)) x_pre) = (0 : Int))) (PreH4 : ((-100000) <= x1_pre)) (PreH5 : (x1_pre <= 100000)) (PreH6 : ((-100000) <= y1_pre)) (PreH7 : (y1_pre <= 100000)) (PreH8 : ((-100000) <= x2_pre)) (PreH9 : (x2_pre <= 100000)) (PreH10 : ((-100000) <= y2_pre)) (PreH11 : (y2_pre <= 100000)) (PreH12 : (1 <= x_pre)) (PreH13 : (x_pre <= 100000)) (PreH14 : (1 <= y_pre)) (PreH15 : (y_pre <= 100000)) ,
  TT && emp 
|--
  “ (Spec x1_pre y1_pre x2_pre y2_pre x_pre y_pre 1) ”
  &&  emp
)

noncomputable def solver_return_wit_2_split_goal_1 : Prop :=
  forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : ((Z.rem (Z.quot (AbsDiff (x1_pre) (x2_pre)) x_pre) 2) = (Z.rem (Z.quot (AbsDiff (y1_pre) (y2_pre)) y_pre) 2))) (PreH2 : ((Z.rem (AbsDiff (y1_pre) (y2_pre)) y_pre) = (0 : Int))) (PreH3 : ((Z.rem (AbsDiff (x1_pre) (x2_pre)) x_pre) = (0 : Int))) (PreH4 : ((-100000) <= x1_pre)) (PreH5 : (x1_pre <= 100000)) (PreH6 : ((-100000) <= y1_pre)) (PreH7 : (y1_pre <= 100000)) (PreH8 : ((-100000) <= x2_pre)) (PreH9 : (x2_pre <= 100000)) (PreH10 : ((-100000) <= y2_pre)) (PreH11 : (y2_pre <= 100000)) (PreH12 : (1 <= x_pre)) (PreH13 : (x_pre <= 100000)) (PreH14 : (1 <= y_pre)) (PreH15 : (y_pre <= 100000)) ,
  (Spec x1_pre y1_pre x2_pre y2_pre x_pre y_pre 1)

noncomputable def solver_return_wit_3 : Prop :=
  (
forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : ((Z.rem (AbsDiff (x1_pre) (x2_pre)) x_pre) ≠ (0 : Int))) (PreH2 : ((AbsDiff (y1_pre) (y2_pre)) = (AbsDiff (y1_pre) (y2_pre)))) (PreH3 : ((-100000) <= x1_pre)) (PreH4 : (x1_pre <= 100000)) (PreH5 : ((-100000) <= y1_pre)) (PreH6 : (y1_pre <= 100000)) (PreH7 : ((-100000) <= x2_pre)) (PreH8 : (x2_pre <= 100000)) (PreH9 : ((-100000) <= y2_pre)) (PreH10 : (y2_pre <= 100000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= 100000)) (PreH13 : (1 <= y_pre)) (PreH14 : (y_pre <= 100000)) ,
  TT && emp 
|--
  “ (Spec x1_pre y1_pre x2_pre y2_pre x_pre y_pre (0 : Int)) ”
  &&  emp
) \/
(
forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : ((Z.rem (AbsDiff (x1_pre) (x2_pre)) x_pre) ≠ (0 : Int))) (PreH2 : ((-100000) <= x1_pre)) (PreH3 : (x1_pre <= 100000)) (PreH4 : ((-100000) <= y1_pre)) (PreH5 : (y1_pre <= 100000)) (PreH6 : ((-100000) <= x2_pre)) (PreH7 : (x2_pre <= 100000)) (PreH8 : ((-100000) <= y2_pre)) (PreH9 : (y2_pre <= 100000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= 100000)) (PreH12 : (1 <= y_pre)) (PreH13 : (y_pre <= 100000)) ,
  TT && emp 
|--
  “ (Spec x1_pre y1_pre x2_pre y2_pre x_pre y_pre (0 : Int)) ”
  &&  emp
)

noncomputable def solver_return_wit_3_split_goal_1 : Prop :=
  forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : ((Z.rem (AbsDiff (x1_pre) (x2_pre)) x_pre) ≠ (0 : Int))) (PreH2 : ((-100000) <= x1_pre)) (PreH3 : (x1_pre <= 100000)) (PreH4 : ((-100000) <= y1_pre)) (PreH5 : (y1_pre <= 100000)) (PreH6 : ((-100000) <= x2_pre)) (PreH7 : (x2_pre <= 100000)) (PreH8 : ((-100000) <= y2_pre)) (PreH9 : (y2_pre <= 100000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= 100000)) (PreH12 : (1 <= y_pre)) (PreH13 : (y_pre <= 100000)) ,
  (Spec x1_pre y1_pre x2_pre y2_pre x_pre y_pre (0 : Int))

noncomputable def solver_return_wit_4 : Prop :=
  (
forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : ((Z.rem (AbsDiff (y1_pre) (y2_pre)) y_pre) ≠ (0 : Int))) (PreH2 : ((Z.rem (AbsDiff (x1_pre) (x2_pre)) x_pre) = (0 : Int))) (PreH3 : ((AbsDiff (y1_pre) (y2_pre)) = (AbsDiff (y1_pre) (y2_pre)))) (PreH4 : ((-100000) <= x1_pre)) (PreH5 : (x1_pre <= 100000)) (PreH6 : ((-100000) <= y1_pre)) (PreH7 : (y1_pre <= 100000)) (PreH8 : ((-100000) <= x2_pre)) (PreH9 : (x2_pre <= 100000)) (PreH10 : ((-100000) <= y2_pre)) (PreH11 : (y2_pre <= 100000)) (PreH12 : (1 <= x_pre)) (PreH13 : (x_pre <= 100000)) (PreH14 : (1 <= y_pre)) (PreH15 : (y_pre <= 100000)) ,
  TT && emp 
|--
  “ (Spec x1_pre y1_pre x2_pre y2_pre x_pre y_pre (0 : Int)) ”
  &&  emp
) \/
(
forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : ((Z.rem (AbsDiff (y1_pre) (y2_pre)) y_pre) ≠ (0 : Int))) (PreH2 : ((Z.rem (AbsDiff (x1_pre) (x2_pre)) x_pre) = (0 : Int))) (PreH3 : ((-100000) <= x1_pre)) (PreH4 : (x1_pre <= 100000)) (PreH5 : ((-100000) <= y1_pre)) (PreH6 : (y1_pre <= 100000)) (PreH7 : ((-100000) <= x2_pre)) (PreH8 : (x2_pre <= 100000)) (PreH9 : ((-100000) <= y2_pre)) (PreH10 : (y2_pre <= 100000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= 100000)) (PreH13 : (1 <= y_pre)) (PreH14 : (y_pre <= 100000)) ,
  TT && emp 
|--
  “ (Spec x1_pre y1_pre x2_pre y2_pre x_pre y_pre (0 : Int)) ”
  &&  emp
)

noncomputable def solver_return_wit_4_split_goal_1 : Prop :=
  forall (x1_pre : Int) (y1_pre : Int) (x2_pre : Int) (y2_pre : Int) (x_pre : Int) (y_pre : Int) (PreH1 : ((Z.rem (AbsDiff (y1_pre) (y2_pre)) y_pre) ≠ (0 : Int))) (PreH2 : ((Z.rem (AbsDiff (x1_pre) (x2_pre)) x_pre) = (0 : Int))) (PreH3 : ((-100000) <= x1_pre)) (PreH4 : (x1_pre <= 100000)) (PreH5 : ((-100000) <= y1_pre)) (PreH6 : (y1_pre <= 100000)) (PreH7 : ((-100000) <= x2_pre)) (PreH8 : (x2_pre <= 100000)) (PreH9 : ((-100000) <= y2_pre)) (PreH10 : (y2_pre <= 100000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= 100000)) (PreH13 : (1 <= y_pre)) (PreH14 : (y_pre <= 100000)) ,
  (Spec x1_pre y1_pre x2_pre y2_pre x_pre y_pre (0 : Int))


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
  proof_of_solver_entail_wit_1_1 : solver_entail_wit_1_1
  proof_of_solver_entail_wit_1_2 : solver_entail_wit_1_2
  proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1
  proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2
  proof_of_solver_return_wit_1 : solver_return_wit_1
  proof_of_solver_return_wit_2 : solver_return_wit_2
  proof_of_solver_return_wit_3 : solver_return_wit_3
  proof_of_solver_return_wit_4 : solver_return_wit_4

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P029_817A_treasure_hunt_goal
