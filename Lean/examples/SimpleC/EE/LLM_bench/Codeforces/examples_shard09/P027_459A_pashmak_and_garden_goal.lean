import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P027_459A_pashmak_and_garden_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P027_459A_pashmak_and_garden_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P027_459A_pashmak_and_garden_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P027_459A_pashmak_and_garden_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def iabs_safety_wit_1 : Prop :=
  forall (x_pre : Int) (PreH1 : (x_pre < (0 : Int))) (PreH2 : ((-200) <= x_pre)) (PreH3 : (x_pre <= 200)) ,
  ((( &( "x" ) )) # Int |-> (x_pre))
|--
  “ (x_pre ≠ (INT_MIN)) ”

noncomputable def iabs_safety_wit_2 : Prop :=
  forall (x_pre : Int) (PreH1 : ((-200) <= x_pre)) (PreH2 : (x_pre <= 200)) ,
  ((( &( "x" ) )) # Int |-> (x_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def iabs_return_wit_1 : Prop :=
  (
forall (x_pre : Int) (PreH1 : (x_pre < (0 : Int))) (PreH2 : ((-200) <= x_pre)) (PreH3 : (x_pre <= 200)) ,
  TT && emp 
|--
  “ ((-x_pre) = (Z.abs (x_pre))) ”
  &&  emp
) \/
(
forall (x_pre : Int) (PreH1 : (x_pre < (0 : Int))) (PreH2 : ((-200) <= x_pre)) (PreH3 : (x_pre <= 200)) ,
  TT && emp 
|--
  “ ((-x_pre) = (Z.abs (x_pre))) ”
  &&  emp
)

noncomputable def iabs_return_wit_1_split_goal_1 : Prop :=
  forall (x_pre : Int) (PreH1 : (x_pre < (0 : Int))) (PreH2 : ((-200) <= x_pre)) (PreH3 : (x_pre <= 200)) ,
  ((-x_pre) = (Z.abs (x_pre)))

noncomputable def iabs_return_wit_2 : Prop :=
  (
forall (x_pre : Int) (PreH1 : (x_pre >= (0 : Int))) (PreH2 : ((-200) <= x_pre)) (PreH3 : (x_pre <= 200)) ,
  TT && emp 
|--
  “ (x_pre = (Z.abs (x_pre))) ”
  &&  emp
) \/
(
forall (x_pre : Int) (PreH1 : (x_pre >= (0 : Int))) (PreH2 : ((-200) <= x_pre)) (PreH3 : (x_pre <= 200)) ,
  TT && emp 
|--
  “ (x_pre = (Z.abs (x_pre))) ”
  &&  emp
)

noncomputable def iabs_return_wit_2_split_goal_1 : Prop :=
  forall (x_pre : Int) (PreH1 : (x_pre >= (0 : Int))) (PreH2 : ((-200) <= x_pre)) (PreH3 : (x_pre <= 200)) ,
  (x_pre = (Z.abs (x_pre)))

noncomputable def solver_safety_wit_1 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (PreH1 : (x1_pre = x2_pre)) (PreH2 : ((-100) <= x1_pre)) (PreH3 : (x1_pre <= 100)) (PreH4 : ((-100) <= y1_pre)) (PreH5 : (y1_pre <= 100)) (PreH6 : ((-100) <= x2_pre)) (PreH7 : (x2_pre <= 100)) (PreH8 : ((-100) <= y2_pre)) (PreH9 : (y2_pre <= 100)) (PreH10 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  ((( &( "d" ) )) # Int |->_)
  ** ((( &( "x1" ) )) # Int |-> (x1_pre))
  ** ((( &( "y1" ) )) # Int |-> (y1_pre))
  ** ((( &( "x2" ) )) # Int |-> (x2_pre))
  ** ((( &( "y2" ) )) # Int |-> (y2_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (intArray.undef_full out_pre 4)
|--
  “ ((y1_pre - y2_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (y1_pre - y2_pre)) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (PreH1 : (retval = (Z.abs ((y1_pre - y2_pre))))) (PreH2 : (x1_pre = x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  ((( &( "d" ) )) # Int |-> (retval))
  ** ((( &( "x1" ) )) # Int |-> (x1_pre))
  ** ((( &( "y1" ) )) # Int |-> (y1_pre))
  ** ((( &( "x2" ) )) # Int |-> (x2_pre))
  ** ((( &( "y2" ) )) # Int |-> (y2_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (intArray.undef_full out_pre 4)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_3 : Prop :=
  (
forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (PreH1 : (retval = (Z.abs ((y1_pre - y2_pre))))) (PreH2 : (x1_pre = x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  ((( &( "d" ) )) # Int |-> (retval))
  ** ((( &( "x1" ) )) # Int |-> (x1_pre))
  ** ((( &( "y1" ) )) # Int |-> (y1_pre))
  ** ((( &( "x2" ) )) # Int |-> (x2_pre))
  ** ((( &( "y2" ) )) # Int |-> (y2_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (intArray.undef_full out_pre 4)
|--
  “ ((x1_pre + retval) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (x1_pre + retval)) ”
) \/
(
forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (PreH1 : (retval = (Z.abs ((y1_pre - y2_pre))))) (PreH2 : (x1_pre = x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  ((( &( "d" ) )) # Int |-> (retval))
  ** ((( &( "x1" ) )) # Int |-> (x1_pre))
  ** ((( &( "y1" ) )) # Int |-> (y1_pre))
  ** ((( &( "x2" ) )) # Int |-> (x2_pre))
  ** ((( &( "y2" ) )) # Int |-> (y2_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (intArray.undef_full out_pre 4)
|--
  “ ((x1_pre + retval) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (x1_pre + retval)) ”
)

noncomputable def solver_safety_wit_3_split_goal_1 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (PreH1 : (retval = (Z.abs ((y1_pre - y2_pre))))) (PreH2 : (x1_pre = x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  ((( &( "d" ) )) # Int |-> (retval))
  ** ((( &( "x1" ) )) # Int |-> (x1_pre))
  ** ((( &( "y1" ) )) # Int |-> (y1_pre))
  ** ((( &( "x2" ) )) # Int |-> (x2_pre))
  ** ((( &( "y2" ) )) # Int |-> (y2_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (intArray.undef_full out_pre 4)
|--
  “ ((x1_pre + retval) <= INT_MAX) ”

noncomputable def solver_safety_wit_3_split_goal_2 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (PreH1 : (retval = (Z.abs ((y1_pre - y2_pre))))) (PreH2 : (x1_pre = x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  ((( &( "d" ) )) # Int |-> (retval))
  ** ((( &( "x1" ) )) # Int |-> (x1_pre))
  ** ((( &( "y1" ) )) # Int |-> (y1_pre))
  ** ((( &( "x2" ) )) # Int |-> (x2_pre))
  ** ((( &( "y2" ) )) # Int |-> (y2_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (intArray.undef_full out_pre 4)
|--
  “ ((INT_MIN) <= (x1_pre + retval)) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (PreH1 : (retval = (Z.abs ((y1_pre - y2_pre))))) (PreH2 : (x1_pre = x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((x1_pre + retval)))
  ** (intArray.undef_seg out_pre 1 4)
  ** ((( &( "d" ) )) # Int |-> (retval))
  ** ((( &( "x1" ) )) # Int |-> (x1_pre))
  ** ((( &( "y1" ) )) # Int |-> (y1_pre))
  ** ((( &( "x2" ) )) # Int |-> (x2_pre))
  ** ((( &( "y2" ) )) # Int |-> (y2_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (PreH1 : (retval = (Z.abs ((y1_pre - y2_pre))))) (PreH2 : (x1_pre = x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (((out_pre + (1 * sizeof(INT)))) # Int |-> (y1_pre))
  ** (intArray.undef_seg out_pre (1 + 1) 4)
  ** (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((x1_pre + retval)))
  ** ((( &( "d" ) )) # Int |-> (retval))
  ** ((( &( "x1" ) )) # Int |-> (x1_pre))
  ** ((( &( "y1" ) )) # Int |-> (y1_pre))
  ** ((( &( "x2" ) )) # Int |-> (x2_pre))
  ** ((( &( "y2" ) )) # Int |-> (y2_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (PreH1 : (retval = (Z.abs ((y1_pre - y2_pre))))) (PreH2 : (x1_pre = x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (((out_pre + (1 * sizeof(INT)))) # Int |-> (y1_pre))
  ** (intArray.undef_seg out_pre (1 + 1) 4)
  ** (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((x1_pre + retval)))
  ** ((( &( "d" ) )) # Int |-> (retval))
  ** ((( &( "x1" ) )) # Int |-> (x1_pre))
  ** ((( &( "y1" ) )) # Int |-> (y1_pre))
  ** ((( &( "x2" ) )) # Int |-> (x2_pre))
  ** ((( &( "y2" ) )) # Int |-> (y2_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
|--
  “ ((x2_pre + retval) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (x2_pre + retval)) ”

noncomputable def solver_safety_wit_7 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (PreH1 : (retval = (Z.abs ((y1_pre - y2_pre))))) (PreH2 : (x1_pre = x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (intArray.undef_seg out_pre ((1 + 1) + 1) 4)
  ** (((out_pre + (2 * sizeof(INT)))) # Int |-> ((x2_pre + retval)))
  ** (((out_pre + (1 * sizeof(INT)))) # Int |-> (y1_pre))
  ** (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((x1_pre + retval)))
  ** ((( &( "d" ) )) # Int |-> (retval))
  ** ((( &( "x1" ) )) # Int |-> (x1_pre))
  ** ((( &( "y1" ) )) # Int |-> (y1_pre))
  ** ((( &( "x2" ) )) # Int |-> (x2_pre))
  ** ((( &( "y2" ) )) # Int |-> (y2_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
|--
  “ (3 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 3) ”

noncomputable def solver_safety_wit_8 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (PreH1 : (retval = (Z.abs ((y1_pre - y2_pre))))) (PreH2 : (x1_pre = x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (intArray.undef_seg out_pre (((1 + 1) + 1) + 1) 4)
  ** (((out_pre + (3 * sizeof(INT)))) # Int |-> (y2_pre))
  ** (((out_pre + (2 * sizeof(INT)))) # Int |-> ((x2_pre + retval)))
  ** (((out_pre + (1 * sizeof(INT)))) # Int |-> (y1_pre))
  ** (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((x1_pre + retval)))
  ** ((( &( "d" ) )) # Int |-> (retval))
  ** ((( &( "x1" ) )) # Int |-> (x1_pre))
  ** ((( &( "y1" ) )) # Int |-> (y1_pre))
  ** ((( &( "x2" ) )) # Int |-> (x2_pre))
  ** ((( &( "y2" ) )) # Int |-> (y2_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_9 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (PreH1 : (y1_pre = y2_pre)) (PreH2 : (x1_pre ≠ x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  ((( &( "d" ) )) # Int |->_)
  ** ((( &( "x1" ) )) # Int |-> (x1_pre))
  ** ((( &( "y1" ) )) # Int |-> (y1_pre))
  ** ((( &( "x2" ) )) # Int |-> (x2_pre))
  ** ((( &( "y2" ) )) # Int |-> (y2_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (intArray.undef_full out_pre 4)
|--
  “ ((x1_pre - x2_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (x1_pre - x2_pre)) ”

noncomputable def solver_safety_wit_10 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (PreH1 : (retval = (Z.abs ((x1_pre - x2_pre))))) (PreH2 : (y1_pre = y2_pre)) (PreH3 : (x1_pre ≠ x2_pre)) (PreH4 : ((-100) <= x1_pre)) (PreH5 : (x1_pre <= 100)) (PreH6 : ((-100) <= y1_pre)) (PreH7 : (y1_pre <= 100)) (PreH8 : ((-100) <= x2_pre)) (PreH9 : (x2_pre <= 100)) (PreH10 : ((-100) <= y2_pre)) (PreH11 : (y2_pre <= 100)) (PreH12 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  ((( &( "d" ) )) # Int |-> (retval))
  ** ((( &( "x1" ) )) # Int |-> (x1_pre))
  ** ((( &( "y1" ) )) # Int |-> (y1_pre))
  ** ((( &( "x2" ) )) # Int |-> (x2_pre))
  ** ((( &( "y2" ) )) # Int |-> (y2_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (intArray.undef_full out_pre 4)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_11 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (PreH1 : (retval = (Z.abs ((x1_pre - x2_pre))))) (PreH2 : (y1_pre = y2_pre)) (PreH3 : (x1_pre ≠ x2_pre)) (PreH4 : ((-100) <= x1_pre)) (PreH5 : (x1_pre <= 100)) (PreH6 : ((-100) <= y1_pre)) (PreH7 : (y1_pre <= 100)) (PreH8 : ((-100) <= x2_pre)) (PreH9 : (x2_pre <= 100)) (PreH10 : ((-100) <= y2_pre)) (PreH11 : (y2_pre <= 100)) (PreH12 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> (x1_pre))
  ** (intArray.undef_seg out_pre 1 4)
  ** ((( &( "d" ) )) # Int |-> (retval))
  ** ((( &( "x1" ) )) # Int |-> (x1_pre))
  ** ((( &( "y1" ) )) # Int |-> (y1_pre))
  ** ((( &( "x2" ) )) # Int |-> (x2_pre))
  ** ((( &( "y2" ) )) # Int |-> (y2_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_12 : Prop :=
  (
forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (PreH1 : (retval = (Z.abs ((x1_pre - x2_pre))))) (PreH2 : (y1_pre = y2_pre)) (PreH3 : (x1_pre ≠ x2_pre)) (PreH4 : ((-100) <= x1_pre)) (PreH5 : (x1_pre <= 100)) (PreH6 : ((-100) <= y1_pre)) (PreH7 : (y1_pre <= 100)) (PreH8 : ((-100) <= x2_pre)) (PreH9 : (x2_pre <= 100)) (PreH10 : ((-100) <= y2_pre)) (PreH11 : (y2_pre <= 100)) (PreH12 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> (x1_pre))
  ** (intArray.undef_seg out_pre 1 4)
  ** ((( &( "d" ) )) # Int |-> (retval))
  ** ((( &( "x1" ) )) # Int |-> (x1_pre))
  ** ((( &( "y1" ) )) # Int |-> (y1_pre))
  ** ((( &( "x2" ) )) # Int |-> (x2_pre))
  ** ((( &( "y2" ) )) # Int |-> (y2_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
|--
  “ ((y1_pre + retval) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (y1_pre + retval)) ”
) \/
(
forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (PreH1 : (retval = (Z.abs ((x1_pre - x2_pre))))) (PreH2 : (y1_pre = y2_pre)) (PreH3 : (x1_pre ≠ x2_pre)) (PreH4 : ((-100) <= x1_pre)) (PreH5 : (x1_pre <= 100)) (PreH6 : ((-100) <= y1_pre)) (PreH7 : (y1_pre <= 100)) (PreH8 : ((-100) <= x2_pre)) (PreH9 : (x2_pre <= 100)) (PreH10 : ((-100) <= y2_pre)) (PreH11 : (y2_pre <= 100)) (PreH12 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> (x1_pre))
  ** (intArray.undef_seg out_pre 1 4)
  ** ((( &( "d" ) )) # Int |-> (retval))
  ** ((( &( "x1" ) )) # Int |-> (x1_pre))
  ** ((( &( "y1" ) )) # Int |-> (y1_pre))
  ** ((( &( "x2" ) )) # Int |-> (x2_pre))
  ** ((( &( "y2" ) )) # Int |-> (y2_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
|--
  “ ((y1_pre + retval) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (y1_pre + retval)) ”
)

noncomputable def solver_safety_wit_12_split_goal_1 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (PreH1 : (retval = (Z.abs ((x1_pre - x2_pre))))) (PreH2 : (y1_pre = y2_pre)) (PreH3 : (x1_pre ≠ x2_pre)) (PreH4 : ((-100) <= x1_pre)) (PreH5 : (x1_pre <= 100)) (PreH6 : ((-100) <= y1_pre)) (PreH7 : (y1_pre <= 100)) (PreH8 : ((-100) <= x2_pre)) (PreH9 : (x2_pre <= 100)) (PreH10 : ((-100) <= y2_pre)) (PreH11 : (y2_pre <= 100)) (PreH12 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> (x1_pre))
  ** (intArray.undef_seg out_pre 1 4)
  ** ((( &( "d" ) )) # Int |-> (retval))
  ** ((( &( "x1" ) )) # Int |-> (x1_pre))
  ** ((( &( "y1" ) )) # Int |-> (y1_pre))
  ** ((( &( "x2" ) )) # Int |-> (x2_pre))
  ** ((( &( "y2" ) )) # Int |-> (y2_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
|--
  “ ((y1_pre + retval) <= INT_MAX) ”

noncomputable def solver_safety_wit_12_split_goal_2 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (PreH1 : (retval = (Z.abs ((x1_pre - x2_pre))))) (PreH2 : (y1_pre = y2_pre)) (PreH3 : (x1_pre ≠ x2_pre)) (PreH4 : ((-100) <= x1_pre)) (PreH5 : (x1_pre <= 100)) (PreH6 : ((-100) <= y1_pre)) (PreH7 : (y1_pre <= 100)) (PreH8 : ((-100) <= x2_pre)) (PreH9 : (x2_pre <= 100)) (PreH10 : ((-100) <= y2_pre)) (PreH11 : (y2_pre <= 100)) (PreH12 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> (x1_pre))
  ** (intArray.undef_seg out_pre 1 4)
  ** ((( &( "d" ) )) # Int |-> (retval))
  ** ((( &( "x1" ) )) # Int |-> (x1_pre))
  ** ((( &( "y1" ) )) # Int |-> (y1_pre))
  ** ((( &( "x2" ) )) # Int |-> (x2_pre))
  ** ((( &( "y2" ) )) # Int |-> (y2_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
|--
  “ ((INT_MIN) <= (y1_pre + retval)) ”

noncomputable def solver_safety_wit_13 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (PreH1 : (retval = (Z.abs ((x1_pre - x2_pre))))) (PreH2 : (y1_pre = y2_pre)) (PreH3 : (x1_pre ≠ x2_pre)) (PreH4 : ((-100) <= x1_pre)) (PreH5 : (x1_pre <= 100)) (PreH6 : ((-100) <= y1_pre)) (PreH7 : (y1_pre <= 100)) (PreH8 : ((-100) <= x2_pre)) (PreH9 : (x2_pre <= 100)) (PreH10 : ((-100) <= y2_pre)) (PreH11 : (y2_pre <= 100)) (PreH12 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (((out_pre + (1 * sizeof(INT)))) # Int |-> ((y1_pre + retval)))
  ** (intArray.undef_seg out_pre (1 + 1) 4)
  ** (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> (x1_pre))
  ** ((( &( "d" ) )) # Int |-> (retval))
  ** ((( &( "x1" ) )) # Int |-> (x1_pre))
  ** ((( &( "y1" ) )) # Int |-> (y1_pre))
  ** ((( &( "x2" ) )) # Int |-> (x2_pre))
  ** ((( &( "y2" ) )) # Int |-> (y2_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_14 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (PreH1 : (retval = (Z.abs ((x1_pre - x2_pre))))) (PreH2 : (y1_pre = y2_pre)) (PreH3 : (x1_pre ≠ x2_pre)) (PreH4 : ((-100) <= x1_pre)) (PreH5 : (x1_pre <= 100)) (PreH6 : ((-100) <= y1_pre)) (PreH7 : (y1_pre <= 100)) (PreH8 : ((-100) <= x2_pre)) (PreH9 : (x2_pre <= 100)) (PreH10 : ((-100) <= y2_pre)) (PreH11 : (y2_pre <= 100)) (PreH12 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (intArray.undef_seg out_pre ((1 + 1) + 1) 4)
  ** (((out_pre + (2 * sizeof(INT)))) # Int |-> (x2_pre))
  ** (((out_pre + (1 * sizeof(INT)))) # Int |-> ((y1_pre + retval)))
  ** (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> (x1_pre))
  ** ((( &( "d" ) )) # Int |-> (retval))
  ** ((( &( "x1" ) )) # Int |-> (x1_pre))
  ** ((( &( "y1" ) )) # Int |-> (y1_pre))
  ** ((( &( "x2" ) )) # Int |-> (x2_pre))
  ** ((( &( "y2" ) )) # Int |-> (y2_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
|--
  “ (3 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 3) ”

noncomputable def solver_safety_wit_15 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (PreH1 : (retval = (Z.abs ((x1_pre - x2_pre))))) (PreH2 : (y1_pre = y2_pre)) (PreH3 : (x1_pre ≠ x2_pre)) (PreH4 : ((-100) <= x1_pre)) (PreH5 : (x1_pre <= 100)) (PreH6 : ((-100) <= y1_pre)) (PreH7 : (y1_pre <= 100)) (PreH8 : ((-100) <= x2_pre)) (PreH9 : (x2_pre <= 100)) (PreH10 : ((-100) <= y2_pre)) (PreH11 : (y2_pre <= 100)) (PreH12 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (intArray.undef_seg out_pre ((1 + 1) + 1) 4)
  ** (((out_pre + (2 * sizeof(INT)))) # Int |-> (x2_pre))
  ** (((out_pre + (1 * sizeof(INT)))) # Int |-> ((y1_pre + retval)))
  ** (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> (x1_pre))
  ** ((( &( "d" ) )) # Int |-> (retval))
  ** ((( &( "x1" ) )) # Int |-> (x1_pre))
  ** ((( &( "y1" ) )) # Int |-> (y1_pre))
  ** ((( &( "x2" ) )) # Int |-> (x2_pre))
  ** ((( &( "y2" ) )) # Int |-> (y2_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
|--
  “ ((y2_pre + retval) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (y2_pre + retval)) ”

noncomputable def solver_safety_wit_16 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (PreH1 : (retval = (Z.abs ((x1_pre - x2_pre))))) (PreH2 : (y1_pre = y2_pre)) (PreH3 : (x1_pre ≠ x2_pre)) (PreH4 : ((-100) <= x1_pre)) (PreH5 : (x1_pre <= 100)) (PreH6 : ((-100) <= y1_pre)) (PreH7 : (y1_pre <= 100)) (PreH8 : ((-100) <= x2_pre)) (PreH9 : (x2_pre <= 100)) (PreH10 : ((-100) <= y2_pre)) (PreH11 : (y2_pre <= 100)) (PreH12 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (intArray.undef_seg out_pre (((1 + 1) + 1) + 1) 4)
  ** (((out_pre + (3 * sizeof(INT)))) # Int |-> ((y2_pre + retval)))
  ** (((out_pre + (2 * sizeof(INT)))) # Int |-> (x2_pre))
  ** (((out_pre + (1 * sizeof(INT)))) # Int |-> ((y1_pre + retval)))
  ** (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> (x1_pre))
  ** ((( &( "d" ) )) # Int |-> (retval))
  ** ((( &( "x1" ) )) # Int |-> (x1_pre))
  ** ((( &( "y1" ) )) # Int |-> (y1_pre))
  ** ((( &( "x2" ) )) # Int |-> (x2_pre))
  ** ((( &( "y2" ) )) # Int |-> (y2_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_17 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (PreH1 : (y1_pre ≠ y2_pre)) (PreH2 : (x1_pre ≠ x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  ((( &( "x1" ) )) # Int |-> (x1_pre))
  ** ((( &( "y1" ) )) # Int |-> (y1_pre))
  ** ((( &( "x2" ) )) # Int |-> (x2_pre))
  ** ((( &( "y2" ) )) # Int |-> (y2_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (intArray.undef_full out_pre 4)
|--
  “ ((x1_pre - x2_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (x1_pre - x2_pre)) ”

noncomputable def solver_safety_wit_18 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (PreH1 : (retval = (Z.abs ((x1_pre - x2_pre))))) (PreH2 : (y1_pre ≠ y2_pre)) (PreH3 : (x1_pre ≠ x2_pre)) (PreH4 : ((-100) <= x1_pre)) (PreH5 : (x1_pre <= 100)) (PreH6 : ((-100) <= y1_pre)) (PreH7 : (y1_pre <= 100)) (PreH8 : ((-100) <= x2_pre)) (PreH9 : (x2_pre <= 100)) (PreH10 : ((-100) <= y2_pre)) (PreH11 : (y2_pre <= 100)) (PreH12 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  ((( &( "x1" ) )) # Int |-> (x1_pre))
  ** ((( &( "y1" ) )) # Int |-> (y1_pre))
  ** ((( &( "x2" ) )) # Int |-> (x2_pre))
  ** ((( &( "y2" ) )) # Int |-> (y2_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (intArray.undef_full out_pre 4)
|--
  “ ((y1_pre - y2_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (y1_pre - y2_pre)) ”

noncomputable def solver_safety_wit_19 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval = retval_2)) (PreH2 : (retval_2 = (Z.abs ((y1_pre - y2_pre))))) (PreH3 : (retval = (Z.abs ((x1_pre - x2_pre))))) (PreH4 : (y1_pre ≠ y2_pre)) (PreH5 : (x1_pre ≠ x2_pre)) (PreH6 : ((-100) <= x1_pre)) (PreH7 : (x1_pre <= 100)) (PreH8 : ((-100) <= y1_pre)) (PreH9 : (y1_pre <= 100)) (PreH10 : ((-100) <= x2_pre)) (PreH11 : (x2_pre <= 100)) (PreH12 : ((-100) <= y2_pre)) (PreH13 : (y2_pre <= 100)) (PreH14 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  ((( &( "x1" ) )) # Int |-> (x1_pre))
  ** ((( &( "y1" ) )) # Int |-> (y1_pre))
  ** ((( &( "x2" ) )) # Int |-> (x2_pre))
  ** ((( &( "y2" ) )) # Int |-> (y2_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (intArray.undef_full out_pre 4)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_20 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval = retval_2)) (PreH2 : (retval_2 = (Z.abs ((y1_pre - y2_pre))))) (PreH3 : (retval = (Z.abs ((x1_pre - x2_pre))))) (PreH4 : (y1_pre ≠ y2_pre)) (PreH5 : (x1_pre ≠ x2_pre)) (PreH6 : ((-100) <= x1_pre)) (PreH7 : (x1_pre <= 100)) (PreH8 : ((-100) <= y1_pre)) (PreH9 : (y1_pre <= 100)) (PreH10 : ((-100) <= x2_pre)) (PreH11 : (x2_pre <= 100)) (PreH12 : ((-100) <= y2_pre)) (PreH13 : (y2_pre <= 100)) (PreH14 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> (x1_pre))
  ** (intArray.undef_seg out_pre 1 4)
  ** ((( &( "x1" ) )) # Int |-> (x1_pre))
  ** ((( &( "y1" ) )) # Int |-> (y1_pre))
  ** ((( &( "x2" ) )) # Int |-> (x2_pre))
  ** ((( &( "y2" ) )) # Int |-> (y2_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_21 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval = retval_2)) (PreH2 : (retval_2 = (Z.abs ((y1_pre - y2_pre))))) (PreH3 : (retval = (Z.abs ((x1_pre - x2_pre))))) (PreH4 : (y1_pre ≠ y2_pre)) (PreH5 : (x1_pre ≠ x2_pre)) (PreH6 : ((-100) <= x1_pre)) (PreH7 : (x1_pre <= 100)) (PreH8 : ((-100) <= y1_pre)) (PreH9 : (y1_pre <= 100)) (PreH10 : ((-100) <= x2_pre)) (PreH11 : (x2_pre <= 100)) (PreH12 : ((-100) <= y2_pre)) (PreH13 : (y2_pre <= 100)) (PreH14 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (((out_pre + (1 * sizeof(INT)))) # Int |-> (y2_pre))
  ** (intArray.undef_seg out_pre (1 + 1) 4)
  ** (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> (x1_pre))
  ** ((( &( "x1" ) )) # Int |-> (x1_pre))
  ** ((( &( "y1" ) )) # Int |-> (y1_pre))
  ** ((( &( "x2" ) )) # Int |-> (x2_pre))
  ** ((( &( "y2" ) )) # Int |-> (y2_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_22 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval = retval_2)) (PreH2 : (retval_2 = (Z.abs ((y1_pre - y2_pre))))) (PreH3 : (retval = (Z.abs ((x1_pre - x2_pre))))) (PreH4 : (y1_pre ≠ y2_pre)) (PreH5 : (x1_pre ≠ x2_pre)) (PreH6 : ((-100) <= x1_pre)) (PreH7 : (x1_pre <= 100)) (PreH8 : ((-100) <= y1_pre)) (PreH9 : (y1_pre <= 100)) (PreH10 : ((-100) <= x2_pre)) (PreH11 : (x2_pre <= 100)) (PreH12 : ((-100) <= y2_pre)) (PreH13 : (y2_pre <= 100)) (PreH14 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (intArray.undef_seg out_pre ((1 + 1) + 1) 4)
  ** (((out_pre + (2 * sizeof(INT)))) # Int |-> (x2_pre))
  ** (((out_pre + (1 * sizeof(INT)))) # Int |-> (y2_pre))
  ** (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> (x1_pre))
  ** ((( &( "x1" ) )) # Int |-> (x1_pre))
  ** ((( &( "y1" ) )) # Int |-> (y1_pre))
  ** ((( &( "x2" ) )) # Int |-> (x2_pre))
  ** ((( &( "y2" ) )) # Int |-> (y2_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
|--
  “ (3 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 3) ”

noncomputable def solver_safety_wit_23 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval = retval_2)) (PreH2 : (retval_2 = (Z.abs ((y1_pre - y2_pre))))) (PreH3 : (retval = (Z.abs ((x1_pre - x2_pre))))) (PreH4 : (y1_pre ≠ y2_pre)) (PreH5 : (x1_pre ≠ x2_pre)) (PreH6 : ((-100) <= x1_pre)) (PreH7 : (x1_pre <= 100)) (PreH8 : ((-100) <= y1_pre)) (PreH9 : (y1_pre <= 100)) (PreH10 : ((-100) <= x2_pre)) (PreH11 : (x2_pre <= 100)) (PreH12 : ((-100) <= y2_pre)) (PreH13 : (y2_pre <= 100)) (PreH14 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (intArray.undef_seg out_pre (((1 + 1) + 1) + 1) 4)
  ** (((out_pre + (3 * sizeof(INT)))) # Int |-> (y1_pre))
  ** (((out_pre + (2 * sizeof(INT)))) # Int |-> (x2_pre))
  ** (((out_pre + (1 * sizeof(INT)))) # Int |-> (y2_pre))
  ** (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> (x1_pre))
  ** ((( &( "x1" ) )) # Int |-> (x1_pre))
  ** ((( &( "y1" ) )) # Int |-> (y1_pre))
  ** ((( &( "x2" ) )) # Int |-> (x2_pre))
  ** ((( &( "y2" ) )) # Int |-> (y2_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_24 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval ≠ retval_2)) (PreH2 : (retval_2 = (Z.abs ((y1_pre - y2_pre))))) (PreH3 : (retval = (Z.abs ((x1_pre - x2_pre))))) (PreH4 : (y1_pre ≠ y2_pre)) (PreH5 : (x1_pre ≠ x2_pre)) (PreH6 : ((-100) <= x1_pre)) (PreH7 : (x1_pre <= 100)) (PreH8 : ((-100) <= y1_pre)) (PreH9 : (y1_pre <= 100)) (PreH10 : ((-100) <= x2_pre)) (PreH11 : (x2_pre <= 100)) (PreH12 : ((-100) <= y2_pre)) (PreH13 : (y2_pre <= 100)) (PreH14 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  ((( &( "x1" ) )) # Int |-> (x1_pre))
  ** ((( &( "y1" ) )) # Int |-> (y1_pre))
  ** ((( &( "x2" ) )) # Int |-> (x2_pre))
  ** ((( &( "y2" ) )) # Int |-> (y2_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (intArray.undef_full out_pre 4)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval ≠ retval_2)) (PreH2 : (retval_2 = (Z.abs ((y1_pre - y2_pre))))) (PreH3 : (retval = (Z.abs ((x1_pre - x2_pre))))) (PreH4 : (y1_pre ≠ y2_pre)) (PreH5 : (x1_pre ≠ x2_pre)) (PreH6 : ((-100) <= x1_pre)) (PreH7 : (x1_pre <= 100)) (PreH8 : ((-100) <= y1_pre)) (PreH9 : (y1_pre <= 100)) (PreH10 : ((-100) <= x2_pre)) (PreH11 : (x2_pre <= 100)) (PreH12 : ((-100) <= y2_pre)) (PreH13 : (y2_pre <= 100)) (PreH14 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (intArray.undef_full out_pre 4)
|--
  “ ((0 : Int) = (0 : Int)) ” &&
  “ (NoCompletion x1_pre y1_pre x2_pre y2_pre) ”
  &&  (intArray.undef_full out_pre 4)
) \/
(
forall (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval ≠ retval_2)) (PreH2 : (retval_2 = (Z.abs ((y1_pre - y2_pre))))) (PreH3 : (retval = (Z.abs ((x1_pre - x2_pre))))) (PreH4 : (y1_pre ≠ y2_pre)) (PreH5 : (x1_pre ≠ x2_pre)) (PreH6 : ((-100) <= x1_pre)) (PreH7 : (x1_pre <= 100)) (PreH8 : ((-100) <= y1_pre)) (PreH9 : (y1_pre <= 100)) (PreH10 : ((-100) <= x2_pre)) (PreH11 : (x2_pre <= 100)) (PreH12 : ((-100) <= y2_pre)) (PreH13 : (y2_pre <= 100)) (PreH14 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  TT && emp 
|--
  “ (NoCompletion x1_pre y1_pre x2_pre y2_pre) ”
  &&  emp
)

noncomputable def solver_return_wit_1_split_goal_1 : Prop :=
  forall (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval ≠ retval_2)) (PreH2 : (retval_2 = (Z.abs ((y1_pre - y2_pre))))) (PreH3 : (retval = (Z.abs ((x1_pre - x2_pre))))) (PreH4 : (y1_pre ≠ y2_pre)) (PreH5 : (x1_pre ≠ x2_pre)) (PreH6 : ((-100) <= x1_pre)) (PreH7 : (x1_pre <= 100)) (PreH8 : ((-100) <= y1_pre)) (PreH9 : (y1_pre <= 100)) (PreH10 : ((-100) <= x2_pre)) (PreH11 : (x2_pre <= 100)) (PreH12 : ((-100) <= y2_pre)) (PreH13 : (y2_pre <= 100)) (PreH14 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (NoCompletion x1_pre y1_pre x2_pre y2_pre)

noncomputable def solver_return_wit_2 : Prop :=
  (
forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval = retval_2)) (PreH2 : (retval_2 = (Z.abs ((y1_pre - y2_pre))))) (PreH3 : (retval = (Z.abs ((x1_pre - x2_pre))))) (PreH4 : (y1_pre ≠ y2_pre)) (PreH5 : (x1_pre ≠ x2_pre)) (PreH6 : ((-100) <= x1_pre)) (PreH7 : (x1_pre <= 100)) (PreH8 : ((-100) <= y1_pre)) (PreH9 : (y1_pre <= 100)) (PreH10 : ((-100) <= x2_pre)) (PreH11 : (x2_pre <= 100)) (PreH12 : ((-100) <= y2_pre)) (PreH13 : (y2_pre <= 100)) (PreH14 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (intArray.undef_seg out_pre (((1 + 1) + 1) + 1) 4)
  ** (((out_pre + (3 * sizeof(INT)))) # Int |-> (y1_pre))
  ** (((out_pre + (2 * sizeof(INT)))) # Int |-> (x2_pre))
  ** (((out_pre + (1 * sizeof(INT)))) # Int |-> (y2_pre))
  ** (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> (x1_pre))
|--
  EX x3 : Int, EX y3 : Int, EX x4 : Int, EX y4 : Int,
  “ (1 = 1) ” &&
  “ (CompletesSquare x1_pre y1_pre x2_pre y2_pre x3 y3 x4 y4) ”
  &&  (intArray.full out_pre 4 (x3 :: (y3 :: (x4 :: (y4 :: (@List.nil Int))))))
) \/
(
forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (x1_pre <= INT_MAX)) (PreH2 : (y2_pre <= INT_MAX)) (PreH3 : (x2_pre <= INT_MAX)) (PreH4 : (y1_pre <= INT_MAX)) (PreH5 : (x1_pre >= INT_MIN)) (PreH6 : (y2_pre >= INT_MIN)) (PreH7 : (x2_pre >= INT_MIN)) (PreH8 : (y1_pre >= INT_MIN)) (PreH9 : (retval = retval_2)) (PreH10 : (retval_2 = (Z.abs ((y1_pre - y2_pre))))) (PreH11 : (retval = (Z.abs ((x1_pre - x2_pre))))) (PreH12 : (y1_pre ≠ y2_pre)) (PreH13 : (x1_pre ≠ x2_pre)) (PreH14 : ((-100) <= x1_pre)) (PreH15 : (x1_pre <= 100)) (PreH16 : ((-100) <= y1_pre)) (PreH17 : (y1_pre <= 100)) (PreH18 : ((-100) <= x2_pre)) (PreH19 : (x2_pre <= 100)) (PreH20 : ((-100) <= y2_pre)) (PreH21 : (y2_pre <= 100)) (PreH22 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (((out_pre + (3 * sizeof(INT)))) # Int |-> (y1_pre))
  ** (((out_pre + (2 * sizeof(INT)))) # Int |-> (x2_pre))
  ** (((out_pre + (1 * sizeof(INT)))) # Int |-> (y2_pre))
  ** (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> (x1_pre))
|--
  EX x3 : Int, EX y3 : Int, EX x4 : Int, EX y4 : Int,
  “ (CompletesSquare x1_pre y1_pre x2_pre y2_pre x3 y3 x4 y4) ”
  &&  (intArray.full out_pre 4 (x3 :: (y3 :: (x4 :: (y4 :: (@List.nil Int))))))
)

noncomputable def solver_return_wit_3 : Prop :=
  (
forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (PreH1 : (retval = (Z.abs ((x1_pre - x2_pre))))) (PreH2 : (y1_pre = y2_pre)) (PreH3 : (x1_pre ≠ x2_pre)) (PreH4 : ((-100) <= x1_pre)) (PreH5 : (x1_pre <= 100)) (PreH6 : ((-100) <= y1_pre)) (PreH7 : (y1_pre <= 100)) (PreH8 : ((-100) <= x2_pre)) (PreH9 : (x2_pre <= 100)) (PreH10 : ((-100) <= y2_pre)) (PreH11 : (y2_pre <= 100)) (PreH12 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (intArray.undef_seg out_pre (((1 + 1) + 1) + 1) 4)
  ** (((out_pre + (3 * sizeof(INT)))) # Int |-> ((y2_pre + retval)))
  ** (((out_pre + (2 * sizeof(INT)))) # Int |-> (x2_pre))
  ** (((out_pre + (1 * sizeof(INT)))) # Int |-> ((y1_pre + retval)))
  ** (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> (x1_pre))
|--
  EX x3 : Int, EX y3 : Int, EX x4 : Int, EX y4 : Int,
  “ (1 = 1) ” &&
  “ (CompletesSquare x1_pre y1_pre x2_pre y2_pre x3 y3 x4 y4) ”
  &&  (intArray.full out_pre 4 (x3 :: (y3 :: (x4 :: (y4 :: (@List.nil Int))))))
) \/
(
forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (PreH1 : (x1_pre <= INT_MAX)) (PreH2 : ((y1_pre + retval) <= INT_MAX)) (PreH3 : (x2_pre <= INT_MAX)) (PreH4 : ((y2_pre + retval) <= INT_MAX)) (PreH5 : (x1_pre >= INT_MIN)) (PreH6 : ((y1_pre + retval) >= INT_MIN)) (PreH7 : (x2_pre >= INT_MIN)) (PreH8 : ((y2_pre + retval) >= INT_MIN)) (PreH9 : (retval = (Z.abs ((x1_pre - x2_pre))))) (PreH10 : (y1_pre = y2_pre)) (PreH11 : (x1_pre ≠ x2_pre)) (PreH12 : ((-100) <= x1_pre)) (PreH13 : (x1_pre <= 100)) (PreH14 : ((-100) <= y1_pre)) (PreH15 : (y1_pre <= 100)) (PreH16 : ((-100) <= x2_pre)) (PreH17 : (x2_pre <= 100)) (PreH18 : ((-100) <= y2_pre)) (PreH19 : (y2_pre <= 100)) (PreH20 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (((out_pre + (3 * sizeof(INT)))) # Int |-> ((y2_pre + retval)))
  ** (((out_pre + (2 * sizeof(INT)))) # Int |-> (x2_pre))
  ** (((out_pre + (1 * sizeof(INT)))) # Int |-> ((y1_pre + retval)))
  ** (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> (x1_pre))
|--
  EX x3 : Int, EX y3 : Int, EX x4 : Int, EX y4 : Int,
  “ (CompletesSquare x1_pre y1_pre x2_pre y2_pre x3 y3 x4 y4) ”
  &&  (intArray.full out_pre 4 (x3 :: (y3 :: (x4 :: (y4 :: (@List.nil Int))))))
)

noncomputable def solver_return_wit_4 : Prop :=
  (
forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (PreH1 : (retval = (Z.abs ((y1_pre - y2_pre))))) (PreH2 : (x1_pre = x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (intArray.undef_seg out_pre (((1 + 1) + 1) + 1) 4)
  ** (((out_pre + (3 * sizeof(INT)))) # Int |-> (y2_pre))
  ** (((out_pre + (2 * sizeof(INT)))) # Int |-> ((x2_pre + retval)))
  ** (((out_pre + (1 * sizeof(INT)))) # Int |-> (y1_pre))
  ** (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((x1_pre + retval)))
|--
  EX x3 : Int, EX y3 : Int, EX x4 : Int, EX y4 : Int,
  “ (1 = 1) ” &&
  “ (CompletesSquare x1_pre y1_pre x2_pre y2_pre x3 y3 x4 y4) ”
  &&  (intArray.full out_pre 4 (x3 :: (y3 :: (x4 :: (y4 :: (@List.nil Int))))))
) \/
(
forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (PreH1 : ((x1_pre + retval) <= INT_MAX)) (PreH2 : (y1_pre <= INT_MAX)) (PreH3 : ((x2_pre + retval) <= INT_MAX)) (PreH4 : (y2_pre <= INT_MAX)) (PreH5 : ((x1_pre + retval) >= INT_MIN)) (PreH6 : (y1_pre >= INT_MIN)) (PreH7 : ((x2_pre + retval) >= INT_MIN)) (PreH8 : (y2_pre >= INT_MIN)) (PreH9 : (retval = (Z.abs ((y1_pre - y2_pre))))) (PreH10 : (x1_pre = x2_pre)) (PreH11 : ((-100) <= x1_pre)) (PreH12 : (x1_pre <= 100)) (PreH13 : ((-100) <= y1_pre)) (PreH14 : (y1_pre <= 100)) (PreH15 : ((-100) <= x2_pre)) (PreH16 : (x2_pre <= 100)) (PreH17 : ((-100) <= y2_pre)) (PreH18 : (y2_pre <= 100)) (PreH19 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (((out_pre + (3 * sizeof(INT)))) # Int |-> (y2_pre))
  ** (((out_pre + (2 * sizeof(INT)))) # Int |-> ((x2_pre + retval)))
  ** (((out_pre + (1 * sizeof(INT)))) # Int |-> (y1_pre))
  ** (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((x1_pre + retval)))
|--
  EX x3 : Int, EX y3 : Int, EX x4 : Int, EX y4 : Int,
  “ (CompletesSquare x1_pre y1_pre x2_pre y2_pre x3 y3 x4 y4) ”
  &&  (intArray.full out_pre 4 (x3 :: (y3 :: (x4 :: (y4 :: (@List.nil Int))))))
)

noncomputable def solver_partial_solve_wit_1_pure : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (PreH1 : (x1_pre = x2_pre)) (PreH2 : ((-100) <= x1_pre)) (PreH3 : (x1_pre <= 100)) (PreH4 : ((-100) <= y1_pre)) (PreH5 : (y1_pre <= 100)) (PreH6 : ((-100) <= x2_pre)) (PreH7 : (x2_pre <= 100)) (PreH8 : ((-100) <= y2_pre)) (PreH9 : (y2_pre <= 100)) (PreH10 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  ((( &( "d" ) )) # Int |->_)
  ** ((( &( "x1" ) )) # Int |-> (x1_pre))
  ** ((( &( "y1" ) )) # Int |-> (y1_pre))
  ** ((( &( "x2" ) )) # Int |-> (x2_pre))
  ** ((( &( "y2" ) )) # Int |-> (y2_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (intArray.undef_full out_pre 4)
|--
  “ ((-200) <= (y1_pre - y2_pre)) ” &&
  “ ((y1_pre - y2_pre) <= 200) ”

noncomputable def solver_partial_solve_wit_1_aux : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (PreH1 : (x1_pre = x2_pre)) (PreH2 : ((-100) <= x1_pre)) (PreH3 : (x1_pre <= 100)) (PreH4 : ((-100) <= y1_pre)) (PreH5 : (y1_pre <= 100)) (PreH6 : ((-100) <= x2_pre)) (PreH7 : (x2_pre <= 100)) (PreH8 : ((-100) <= y2_pre)) (PreH9 : (y2_pre <= 100)) (PreH10 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (intArray.undef_full out_pre 4)
|--
  “ ((-200) <= (y1_pre - y2_pre)) ” &&
  “ ((y1_pre - y2_pre) <= 200) ” &&
  “ (x1_pre = x2_pre) ” &&
  “ ((-100) <= x1_pre) ” &&
  “ (x1_pre <= 100) ” &&
  “ ((-100) <= y1_pre) ” &&
  “ (y1_pre <= 100) ” &&
  “ ((-100) <= x2_pre) ” &&
  “ (x2_pre <= 100) ” &&
  “ ((-100) <= y2_pre) ” &&
  “ (y2_pre <= 100) ” &&
  “ (Pre x1_pre y1_pre x2_pre y2_pre) ”
  &&  (intArray.undef_full out_pre 4)

noncomputable def solver_partial_solve_wit_1 : Prop := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux

noncomputable def solver_partial_solve_wit_2 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (PreH1 : (retval = (Z.abs ((y1_pre - y2_pre))))) (PreH2 : (x1_pre = x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (intArray.undef_full out_pre 4)
|--
  “ (retval = (Z.abs ((y1_pre - y2_pre)))) ” &&
  “ (x1_pre = x2_pre) ” &&
  “ ((-100) <= x1_pre) ” &&
  “ (x1_pre <= 100) ” &&
  “ ((-100) <= y1_pre) ” &&
  “ (y1_pre <= 100) ” &&
  “ ((-100) <= x2_pre) ” &&
  “ (x2_pre <= 100) ” &&
  “ ((-100) <= y2_pre) ” &&
  “ (y2_pre <= 100) ” &&
  “ (Pre x1_pre y1_pre x2_pre y2_pre) ”
  &&  (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg out_pre 1 4)

noncomputable def solver_partial_solve_wit_3 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (PreH1 : (retval = (Z.abs ((y1_pre - y2_pre))))) (PreH2 : (x1_pre = x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((x1_pre + retval)))
  ** (intArray.undef_seg out_pre 1 4)
|--
  “ (retval = (Z.abs ((y1_pre - y2_pre)))) ” &&
  “ (x1_pre = x2_pre) ” &&
  “ ((-100) <= x1_pre) ” &&
  “ (x1_pre <= 100) ” &&
  “ ((-100) <= y1_pre) ” &&
  “ (y1_pre <= 100) ” &&
  “ ((-100) <= x2_pre) ” &&
  “ (x2_pre <= 100) ” &&
  “ ((-100) <= y2_pre) ” &&
  “ (y2_pre <= 100) ” &&
  “ (Pre x1_pre y1_pre x2_pre y2_pre) ”
  &&  (((out_pre + (1 * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg out_pre (1 + 1) 4)
  ** (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((x1_pre + retval)))

noncomputable def solver_partial_solve_wit_4 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (PreH1 : (retval = (Z.abs ((y1_pre - y2_pre))))) (PreH2 : (x1_pre = x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (((out_pre + (1 * sizeof(INT)))) # Int |-> (y1_pre))
  ** (intArray.undef_seg out_pre (1 + 1) 4)
  ** (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((x1_pre + retval)))
|--
  “ (retval = (Z.abs ((y1_pre - y2_pre)))) ” &&
  “ (x1_pre = x2_pre) ” &&
  “ ((-100) <= x1_pre) ” &&
  “ (x1_pre <= 100) ” &&
  “ ((-100) <= y1_pre) ” &&
  “ (y1_pre <= 100) ” &&
  “ ((-100) <= x2_pre) ” &&
  “ (x2_pre <= 100) ” &&
  “ ((-100) <= y2_pre) ” &&
  “ (y2_pre <= 100) ” &&
  “ (Pre x1_pre y1_pre x2_pre y2_pre) ”
  &&  (((out_pre + (2 * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_missing_i out_pre 2 (1 + 1) 4)
  ** (((out_pre + (1 * sizeof(INT)))) # Int |-> (y1_pre))
  ** (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((x1_pre + retval)))

noncomputable def solver_partial_solve_wit_5 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (PreH1 : (retval = (Z.abs ((y1_pre - y2_pre))))) (PreH2 : (x1_pre = x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (intArray.undef_seg out_pre ((1 + 1) + 1) 4)
  ** (((out_pre + (2 * sizeof(INT)))) # Int |-> ((x2_pre + retval)))
  ** (((out_pre + (1 * sizeof(INT)))) # Int |-> (y1_pre))
  ** (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((x1_pre + retval)))
|--
  “ (retval = (Z.abs ((y1_pre - y2_pre)))) ” &&
  “ (x1_pre = x2_pre) ” &&
  “ ((-100) <= x1_pre) ” &&
  “ (x1_pre <= 100) ” &&
  “ ((-100) <= y1_pre) ” &&
  “ (y1_pre <= 100) ” &&
  “ ((-100) <= x2_pre) ” &&
  “ (x2_pre <= 100) ” &&
  “ ((-100) <= y2_pre) ” &&
  “ (y2_pre <= 100) ” &&
  “ (Pre x1_pre y1_pre x2_pre y2_pre) ”
  &&  (((out_pre + (3 * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_missing_i out_pre 3 ((1 + 1) + 1) 4)
  ** (((out_pre + (2 * sizeof(INT)))) # Int |-> ((x2_pre + retval)))
  ** (((out_pre + (1 * sizeof(INT)))) # Int |-> (y1_pre))
  ** (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((x1_pre + retval)))

noncomputable def solver_partial_solve_wit_6_pure : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (PreH1 : (y1_pre = y2_pre)) (PreH2 : (x1_pre ≠ x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  ((( &( "d" ) )) # Int |->_)
  ** ((( &( "x1" ) )) # Int |-> (x1_pre))
  ** ((( &( "y1" ) )) # Int |-> (y1_pre))
  ** ((( &( "x2" ) )) # Int |-> (x2_pre))
  ** ((( &( "y2" ) )) # Int |-> (y2_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (intArray.undef_full out_pre 4)
|--
  “ ((-200) <= (x1_pre - x2_pre)) ” &&
  “ ((x1_pre - x2_pre) <= 200) ”

noncomputable def solver_partial_solve_wit_6_aux : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (PreH1 : (y1_pre = y2_pre)) (PreH2 : (x1_pre ≠ x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (intArray.undef_full out_pre 4)
|--
  “ ((-200) <= (x1_pre - x2_pre)) ” &&
  “ ((x1_pre - x2_pre) <= 200) ” &&
  “ (y1_pre = y2_pre) ” &&
  “ (x1_pre ≠ x2_pre) ” &&
  “ ((-100) <= x1_pre) ” &&
  “ (x1_pre <= 100) ” &&
  “ ((-100) <= y1_pre) ” &&
  “ (y1_pre <= 100) ” &&
  “ ((-100) <= x2_pre) ” &&
  “ (x2_pre <= 100) ” &&
  “ ((-100) <= y2_pre) ” &&
  “ (y2_pre <= 100) ” &&
  “ (Pre x1_pre y1_pre x2_pre y2_pre) ”
  &&  (intArray.undef_full out_pre 4)

noncomputable def solver_partial_solve_wit_6 : Prop := solver_partial_solve_wit_6_pure -> solver_partial_solve_wit_6_aux

noncomputable def solver_partial_solve_wit_7 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (PreH1 : (retval = (Z.abs ((x1_pre - x2_pre))))) (PreH2 : (y1_pre = y2_pre)) (PreH3 : (x1_pre ≠ x2_pre)) (PreH4 : ((-100) <= x1_pre)) (PreH5 : (x1_pre <= 100)) (PreH6 : ((-100) <= y1_pre)) (PreH7 : (y1_pre <= 100)) (PreH8 : ((-100) <= x2_pre)) (PreH9 : (x2_pre <= 100)) (PreH10 : ((-100) <= y2_pre)) (PreH11 : (y2_pre <= 100)) (PreH12 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (intArray.undef_full out_pre 4)
|--
  “ (retval = (Z.abs ((x1_pre - x2_pre)))) ” &&
  “ (y1_pre = y2_pre) ” &&
  “ (x1_pre ≠ x2_pre) ” &&
  “ ((-100) <= x1_pre) ” &&
  “ (x1_pre <= 100) ” &&
  “ ((-100) <= y1_pre) ” &&
  “ (y1_pre <= 100) ” &&
  “ ((-100) <= x2_pre) ” &&
  “ (x2_pre <= 100) ” &&
  “ ((-100) <= y2_pre) ” &&
  “ (y2_pre <= 100) ” &&
  “ (Pre x1_pre y1_pre x2_pre y2_pre) ”
  &&  (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg out_pre 1 4)

noncomputable def solver_partial_solve_wit_8 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (PreH1 : (retval = (Z.abs ((x1_pre - x2_pre))))) (PreH2 : (y1_pre = y2_pre)) (PreH3 : (x1_pre ≠ x2_pre)) (PreH4 : ((-100) <= x1_pre)) (PreH5 : (x1_pre <= 100)) (PreH6 : ((-100) <= y1_pre)) (PreH7 : (y1_pre <= 100)) (PreH8 : ((-100) <= x2_pre)) (PreH9 : (x2_pre <= 100)) (PreH10 : ((-100) <= y2_pre)) (PreH11 : (y2_pre <= 100)) (PreH12 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> (x1_pre))
  ** (intArray.undef_seg out_pre 1 4)
|--
  “ (retval = (Z.abs ((x1_pre - x2_pre)))) ” &&
  “ (y1_pre = y2_pre) ” &&
  “ (x1_pre ≠ x2_pre) ” &&
  “ ((-100) <= x1_pre) ” &&
  “ (x1_pre <= 100) ” &&
  “ ((-100) <= y1_pre) ” &&
  “ (y1_pre <= 100) ” &&
  “ ((-100) <= x2_pre) ” &&
  “ (x2_pre <= 100) ” &&
  “ ((-100) <= y2_pre) ” &&
  “ (y2_pre <= 100) ” &&
  “ (Pre x1_pre y1_pre x2_pre y2_pre) ”
  &&  (((out_pre + (1 * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg out_pre (1 + 1) 4)
  ** (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> (x1_pre))

noncomputable def solver_partial_solve_wit_9 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (PreH1 : (retval = (Z.abs ((x1_pre - x2_pre))))) (PreH2 : (y1_pre = y2_pre)) (PreH3 : (x1_pre ≠ x2_pre)) (PreH4 : ((-100) <= x1_pre)) (PreH5 : (x1_pre <= 100)) (PreH6 : ((-100) <= y1_pre)) (PreH7 : (y1_pre <= 100)) (PreH8 : ((-100) <= x2_pre)) (PreH9 : (x2_pre <= 100)) (PreH10 : ((-100) <= y2_pre)) (PreH11 : (y2_pre <= 100)) (PreH12 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (((out_pre + (1 * sizeof(INT)))) # Int |-> ((y1_pre + retval)))
  ** (intArray.undef_seg out_pre (1 + 1) 4)
  ** (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> (x1_pre))
|--
  “ (retval = (Z.abs ((x1_pre - x2_pre)))) ” &&
  “ (y1_pre = y2_pre) ” &&
  “ (x1_pre ≠ x2_pre) ” &&
  “ ((-100) <= x1_pre) ” &&
  “ (x1_pre <= 100) ” &&
  “ ((-100) <= y1_pre) ” &&
  “ (y1_pre <= 100) ” &&
  “ ((-100) <= x2_pre) ” &&
  “ (x2_pre <= 100) ” &&
  “ ((-100) <= y2_pre) ” &&
  “ (y2_pre <= 100) ” &&
  “ (Pre x1_pre y1_pre x2_pre y2_pre) ”
  &&  (((out_pre + (2 * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_missing_i out_pre 2 (1 + 1) 4)
  ** (((out_pre + (1 * sizeof(INT)))) # Int |-> ((y1_pre + retval)))
  ** (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> (x1_pre))

noncomputable def solver_partial_solve_wit_10 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (PreH1 : (retval = (Z.abs ((x1_pre - x2_pre))))) (PreH2 : (y1_pre = y2_pre)) (PreH3 : (x1_pre ≠ x2_pre)) (PreH4 : ((-100) <= x1_pre)) (PreH5 : (x1_pre <= 100)) (PreH6 : ((-100) <= y1_pre)) (PreH7 : (y1_pre <= 100)) (PreH8 : ((-100) <= x2_pre)) (PreH9 : (x2_pre <= 100)) (PreH10 : ((-100) <= y2_pre)) (PreH11 : (y2_pre <= 100)) (PreH12 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (intArray.undef_seg out_pre ((1 + 1) + 1) 4)
  ** (((out_pre + (2 * sizeof(INT)))) # Int |-> (x2_pre))
  ** (((out_pre + (1 * sizeof(INT)))) # Int |-> ((y1_pre + retval)))
  ** (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> (x1_pre))
|--
  “ (retval = (Z.abs ((x1_pre - x2_pre)))) ” &&
  “ (y1_pre = y2_pre) ” &&
  “ (x1_pre ≠ x2_pre) ” &&
  “ ((-100) <= x1_pre) ” &&
  “ (x1_pre <= 100) ” &&
  “ ((-100) <= y1_pre) ” &&
  “ (y1_pre <= 100) ” &&
  “ ((-100) <= x2_pre) ” &&
  “ (x2_pre <= 100) ” &&
  “ ((-100) <= y2_pre) ” &&
  “ (y2_pre <= 100) ” &&
  “ (Pre x1_pre y1_pre x2_pre y2_pre) ”
  &&  (((out_pre + (3 * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_missing_i out_pre 3 ((1 + 1) + 1) 4)
  ** (((out_pre + (2 * sizeof(INT)))) # Int |-> (x2_pre))
  ** (((out_pre + (1 * sizeof(INT)))) # Int |-> ((y1_pre + retval)))
  ** (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> (x1_pre))

noncomputable def solver_partial_solve_wit_11_pure : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (PreH1 : (y1_pre ≠ y2_pre)) (PreH2 : (x1_pre ≠ x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  ((( &( "x1" ) )) # Int |-> (x1_pre))
  ** ((( &( "y1" ) )) # Int |-> (y1_pre))
  ** ((( &( "x2" ) )) # Int |-> (x2_pre))
  ** ((( &( "y2" ) )) # Int |-> (y2_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (intArray.undef_full out_pre 4)
|--
  “ ((-200) <= (x1_pre - x2_pre)) ” &&
  “ ((x1_pre - x2_pre) <= 200) ”

noncomputable def solver_partial_solve_wit_11_aux : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (PreH1 : (y1_pre ≠ y2_pre)) (PreH2 : (x1_pre ≠ x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (intArray.undef_full out_pre 4)
|--
  “ ((-200) <= (x1_pre - x2_pre)) ” &&
  “ ((x1_pre - x2_pre) <= 200) ” &&
  “ (y1_pre ≠ y2_pre) ” &&
  “ (x1_pre ≠ x2_pre) ” &&
  “ ((-100) <= x1_pre) ” &&
  “ (x1_pre <= 100) ” &&
  “ ((-100) <= y1_pre) ” &&
  “ (y1_pre <= 100) ” &&
  “ ((-100) <= x2_pre) ” &&
  “ (x2_pre <= 100) ” &&
  “ ((-100) <= y2_pre) ” &&
  “ (y2_pre <= 100) ” &&
  “ (Pre x1_pre y1_pre x2_pre y2_pre) ”
  &&  (intArray.undef_full out_pre 4)

noncomputable def solver_partial_solve_wit_11 : Prop := solver_partial_solve_wit_11_pure -> solver_partial_solve_wit_11_aux

noncomputable def solver_partial_solve_wit_12_pure : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (PreH1 : (retval = (Z.abs ((x1_pre - x2_pre))))) (PreH2 : (y1_pre ≠ y2_pre)) (PreH3 : (x1_pre ≠ x2_pre)) (PreH4 : ((-100) <= x1_pre)) (PreH5 : (x1_pre <= 100)) (PreH6 : ((-100) <= y1_pre)) (PreH7 : (y1_pre <= 100)) (PreH8 : ((-100) <= x2_pre)) (PreH9 : (x2_pre <= 100)) (PreH10 : ((-100) <= y2_pre)) (PreH11 : (y2_pre <= 100)) (PreH12 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  ((( &( "x1" ) )) # Int |-> (x1_pre))
  ** ((( &( "y1" ) )) # Int |-> (y1_pre))
  ** ((( &( "x2" ) )) # Int |-> (x2_pre))
  ** ((( &( "y2" ) )) # Int |-> (y2_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (intArray.undef_full out_pre 4)
|--
  “ ((-200) <= (y1_pre - y2_pre)) ” &&
  “ ((y1_pre - y2_pre) <= 200) ”

noncomputable def solver_partial_solve_wit_12_aux : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (PreH1 : (retval = (Z.abs ((x1_pre - x2_pre))))) (PreH2 : (y1_pre ≠ y2_pre)) (PreH3 : (x1_pre ≠ x2_pre)) (PreH4 : ((-100) <= x1_pre)) (PreH5 : (x1_pre <= 100)) (PreH6 : ((-100) <= y1_pre)) (PreH7 : (y1_pre <= 100)) (PreH8 : ((-100) <= x2_pre)) (PreH9 : (x2_pre <= 100)) (PreH10 : ((-100) <= y2_pre)) (PreH11 : (y2_pre <= 100)) (PreH12 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (intArray.undef_full out_pre 4)
|--
  “ ((-200) <= (y1_pre - y2_pre)) ” &&
  “ ((y1_pre - y2_pre) <= 200) ” &&
  “ (retval = (Z.abs ((x1_pre - x2_pre)))) ” &&
  “ (y1_pre ≠ y2_pre) ” &&
  “ (x1_pre ≠ x2_pre) ” &&
  “ ((-100) <= x1_pre) ” &&
  “ (x1_pre <= 100) ” &&
  “ ((-100) <= y1_pre) ” &&
  “ (y1_pre <= 100) ” &&
  “ ((-100) <= x2_pre) ” &&
  “ (x2_pre <= 100) ” &&
  “ ((-100) <= y2_pre) ” &&
  “ (y2_pre <= 100) ” &&
  “ (Pre x1_pre y1_pre x2_pre y2_pre) ”
  &&  (intArray.undef_full out_pre 4)

noncomputable def solver_partial_solve_wit_12 : Prop := solver_partial_solve_wit_12_pure -> solver_partial_solve_wit_12_aux

noncomputable def solver_partial_solve_wit_13 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval = retval_2)) (PreH2 : (retval_2 = (Z.abs ((y1_pre - y2_pre))))) (PreH3 : (retval = (Z.abs ((x1_pre - x2_pre))))) (PreH4 : (y1_pre ≠ y2_pre)) (PreH5 : (x1_pre ≠ x2_pre)) (PreH6 : ((-100) <= x1_pre)) (PreH7 : (x1_pre <= 100)) (PreH8 : ((-100) <= y1_pre)) (PreH9 : (y1_pre <= 100)) (PreH10 : ((-100) <= x2_pre)) (PreH11 : (x2_pre <= 100)) (PreH12 : ((-100) <= y2_pre)) (PreH13 : (y2_pre <= 100)) (PreH14 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (intArray.undef_full out_pre 4)
|--
  “ (retval = retval_2) ” &&
  “ (retval_2 = (Z.abs ((y1_pre - y2_pre)))) ” &&
  “ (retval = (Z.abs ((x1_pre - x2_pre)))) ” &&
  “ (y1_pre ≠ y2_pre) ” &&
  “ (x1_pre ≠ x2_pre) ” &&
  “ ((-100) <= x1_pre) ” &&
  “ (x1_pre <= 100) ” &&
  “ ((-100) <= y1_pre) ” &&
  “ (y1_pre <= 100) ” &&
  “ ((-100) <= x2_pre) ” &&
  “ (x2_pre <= 100) ” &&
  “ ((-100) <= y2_pre) ” &&
  “ (y2_pre <= 100) ” &&
  “ (Pre x1_pre y1_pre x2_pre y2_pre) ”
  &&  (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg out_pre 1 4)

noncomputable def solver_partial_solve_wit_14 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval = retval_2)) (PreH2 : (retval_2 = (Z.abs ((y1_pre - y2_pre))))) (PreH3 : (retval = (Z.abs ((x1_pre - x2_pre))))) (PreH4 : (y1_pre ≠ y2_pre)) (PreH5 : (x1_pre ≠ x2_pre)) (PreH6 : ((-100) <= x1_pre)) (PreH7 : (x1_pre <= 100)) (PreH8 : ((-100) <= y1_pre)) (PreH9 : (y1_pre <= 100)) (PreH10 : ((-100) <= x2_pre)) (PreH11 : (x2_pre <= 100)) (PreH12 : ((-100) <= y2_pre)) (PreH13 : (y2_pre <= 100)) (PreH14 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> (x1_pre))
  ** (intArray.undef_seg out_pre 1 4)
|--
  “ (retval = retval_2) ” &&
  “ (retval_2 = (Z.abs ((y1_pre - y2_pre)))) ” &&
  “ (retval = (Z.abs ((x1_pre - x2_pre)))) ” &&
  “ (y1_pre ≠ y2_pre) ” &&
  “ (x1_pre ≠ x2_pre) ” &&
  “ ((-100) <= x1_pre) ” &&
  “ (x1_pre <= 100) ” &&
  “ ((-100) <= y1_pre) ” &&
  “ (y1_pre <= 100) ” &&
  “ ((-100) <= x2_pre) ” &&
  “ (x2_pre <= 100) ” &&
  “ ((-100) <= y2_pre) ” &&
  “ (y2_pre <= 100) ” &&
  “ (Pre x1_pre y1_pre x2_pre y2_pre) ”
  &&  (((out_pre + (1 * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg out_pre (1 + 1) 4)
  ** (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> (x1_pre))

noncomputable def solver_partial_solve_wit_15 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval = retval_2)) (PreH2 : (retval_2 = (Z.abs ((y1_pre - y2_pre))))) (PreH3 : (retval = (Z.abs ((x1_pre - x2_pre))))) (PreH4 : (y1_pre ≠ y2_pre)) (PreH5 : (x1_pre ≠ x2_pre)) (PreH6 : ((-100) <= x1_pre)) (PreH7 : (x1_pre <= 100)) (PreH8 : ((-100) <= y1_pre)) (PreH9 : (y1_pre <= 100)) (PreH10 : ((-100) <= x2_pre)) (PreH11 : (x2_pre <= 100)) (PreH12 : ((-100) <= y2_pre)) (PreH13 : (y2_pre <= 100)) (PreH14 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (((out_pre + (1 * sizeof(INT)))) # Int |-> (y2_pre))
  ** (intArray.undef_seg out_pre (1 + 1) 4)
  ** (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> (x1_pre))
|--
  “ (retval = retval_2) ” &&
  “ (retval_2 = (Z.abs ((y1_pre - y2_pre)))) ” &&
  “ (retval = (Z.abs ((x1_pre - x2_pre)))) ” &&
  “ (y1_pre ≠ y2_pre) ” &&
  “ (x1_pre ≠ x2_pre) ” &&
  “ ((-100) <= x1_pre) ” &&
  “ (x1_pre <= 100) ” &&
  “ ((-100) <= y1_pre) ” &&
  “ (y1_pre <= 100) ” &&
  “ ((-100) <= x2_pre) ” &&
  “ (x2_pre <= 100) ” &&
  “ ((-100) <= y2_pre) ” &&
  “ (y2_pre <= 100) ” &&
  “ (Pre x1_pre y1_pre x2_pre y2_pre) ”
  &&  (((out_pre + (2 * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_missing_i out_pre 2 (1 + 1) 4)
  ** (((out_pre + (1 * sizeof(INT)))) # Int |-> (y2_pre))
  ** (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> (x1_pre))

noncomputable def solver_partial_solve_wit_16 : Prop :=
  forall (out_pre : Int) (y2_pre : Int) (x2_pre : Int) (y1_pre : Int) (x1_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval = retval_2)) (PreH2 : (retval_2 = (Z.abs ((y1_pre - y2_pre))))) (PreH3 : (retval = (Z.abs ((x1_pre - x2_pre))))) (PreH4 : (y1_pre ≠ y2_pre)) (PreH5 : (x1_pre ≠ x2_pre)) (PreH6 : ((-100) <= x1_pre)) (PreH7 : (x1_pre <= 100)) (PreH8 : ((-100) <= y1_pre)) (PreH9 : (y1_pre <= 100)) (PreH10 : ((-100) <= x2_pre)) (PreH11 : (x2_pre <= 100)) (PreH12 : ((-100) <= y2_pre)) (PreH13 : (y2_pre <= 100)) (PreH14 : (Pre x1_pre y1_pre x2_pre y2_pre)) ,
  (intArray.undef_seg out_pre ((1 + 1) + 1) 4)
  ** (((out_pre + (2 * sizeof(INT)))) # Int |-> (x2_pre))
  ** (((out_pre + (1 * sizeof(INT)))) # Int |-> (y2_pre))
  ** (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> (x1_pre))
|--
  “ (retval = retval_2) ” &&
  “ (retval_2 = (Z.abs ((y1_pre - y2_pre)))) ” &&
  “ (retval = (Z.abs ((x1_pre - x2_pre)))) ” &&
  “ (y1_pre ≠ y2_pre) ” &&
  “ (x1_pre ≠ x2_pre) ” &&
  “ ((-100) <= x1_pre) ” &&
  “ (x1_pre <= 100) ” &&
  “ ((-100) <= y1_pre) ” &&
  “ (y1_pre <= 100) ” &&
  “ ((-100) <= x2_pre) ” &&
  “ (x2_pre <= 100) ” &&
  “ ((-100) <= y2_pre) ” &&
  “ (y2_pre <= 100) ” &&
  “ (Pre x1_pre y1_pre x2_pre y2_pre) ”
  &&  (((out_pre + (3 * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_missing_i out_pre 3 ((1 + 1) + 1) 4)
  ** (((out_pre + (2 * sizeof(INT)))) # Int |-> (x2_pre))
  ** (((out_pre + (1 * sizeof(INT)))) # Int |-> (y2_pre))
  ** (((out_pre + ((0 : Int) * sizeof(INT)))) # Int |-> (x1_pre))


structure VC_Correct : Type where
  proof_of_iabs_safety_wit_1 : iabs_safety_wit_1
  proof_of_iabs_safety_wit_2 : iabs_safety_wit_2
  proof_of_solver_safety_wit_1 : solver_safety_wit_1
  proof_of_solver_safety_wit_2 : solver_safety_wit_2
  proof_of_solver_safety_wit_4 : solver_safety_wit_4
  proof_of_solver_safety_wit_5 : solver_safety_wit_5
  proof_of_solver_safety_wit_6 : solver_safety_wit_6
  proof_of_solver_safety_wit_7 : solver_safety_wit_7
  proof_of_solver_safety_wit_8 : solver_safety_wit_8
  proof_of_solver_safety_wit_9 : solver_safety_wit_9
  proof_of_solver_safety_wit_10 : solver_safety_wit_10
  proof_of_solver_safety_wit_11 : solver_safety_wit_11
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
  proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2
  proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3
  proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4
  proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5
  proof_of_solver_partial_solve_wit_6_pure : solver_partial_solve_wit_6_pure
  proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6
  proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7
  proof_of_solver_partial_solve_wit_8 : solver_partial_solve_wit_8
  proof_of_solver_partial_solve_wit_9 : solver_partial_solve_wit_9
  proof_of_solver_partial_solve_wit_10 : solver_partial_solve_wit_10
  proof_of_solver_partial_solve_wit_11_pure : solver_partial_solve_wit_11_pure
  proof_of_solver_partial_solve_wit_11 : solver_partial_solve_wit_11
  proof_of_solver_partial_solve_wit_12_pure : solver_partial_solve_wit_12_pure
  proof_of_solver_partial_solve_wit_12 : solver_partial_solve_wit_12
  proof_of_solver_partial_solve_wit_13 : solver_partial_solve_wit_13
  proof_of_solver_partial_solve_wit_14 : solver_partial_solve_wit_14
  proof_of_solver_partial_solve_wit_15 : solver_partial_solve_wit_15
  proof_of_solver_partial_solve_wit_16 : solver_partial_solve_wit_16
  proof_of_iabs_return_wit_1 : iabs_return_wit_1
  proof_of_iabs_return_wit_2 : iabs_return_wit_2
  proof_of_solver_safety_wit_3 : solver_safety_wit_3
  proof_of_solver_safety_wit_12 : solver_safety_wit_12
  proof_of_solver_return_wit_1 : solver_return_wit_1
  proof_of_solver_return_wit_2 : solver_return_wit_2
  proof_of_solver_return_wit_3 : solver_return_wit_3
  proof_of_solver_return_wit_4 : solver_return_wit_4

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P027_459A_pashmak_and_garden_goal
