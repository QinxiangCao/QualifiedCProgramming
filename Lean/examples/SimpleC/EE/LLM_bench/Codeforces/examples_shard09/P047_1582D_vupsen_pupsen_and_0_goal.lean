import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P047_1582D_vupsen_pupsen_and_0_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P047_1582D_vupsen_pupsen_and_0_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P047_1582D_vupsen_pupsen_and_0_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P047_1582D_vupsen_pupsen_and_0_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def llabs_safety_wit_1 : Prop :=
  forall (x_pre : Int) (PreH1 : (x_pre < (0 : Int))) (PreH2 : ((-10000) <= x_pre)) (PreH3 : (x_pre <= 10000)) ,
  ((( &( "x" ) )) # Int64 |-> (x_pre))
|--
  “ (x_pre ≠ (-9223372036854775808)) ”

noncomputable def llabs_safety_wit_2 : Prop :=
  forall (x_pre : Int) (PreH1 : ((-10000) <= x_pre)) (PreH2 : (x_pre <= 10000)) ,
  ((( &( "x" ) )) # Int64 |-> (x_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def llabs_return_wit_1 : Prop :=
  (
forall (x_pre : Int) (PreH1 : (x_pre < (0 : Int))) (PreH2 : ((-10000) <= x_pre)) (PreH3 : (x_pre <= 10000)) ,
  TT && emp 
|--
  “ ((-x_pre) = (Z.abs (x_pre))) ”
  &&  emp
) \/
(
forall (x_pre : Int) (PreH1 : (x_pre < (0 : Int))) (PreH2 : ((-10000) <= x_pre)) (PreH3 : (x_pre <= 10000)) ,
  TT && emp 
|--
  “ ((-x_pre) = (Z.abs (x_pre))) ”
  &&  emp
)

noncomputable def llabs_return_wit_1_split_goal_1 : Prop :=
  forall (x_pre : Int) (PreH1 : (x_pre < (0 : Int))) (PreH2 : ((-10000) <= x_pre)) (PreH3 : (x_pre <= 10000)) ,
  ((-x_pre) = (Z.abs (x_pre)))

noncomputable def llabs_return_wit_2 : Prop :=
  (
forall (x_pre : Int) (PreH1 : (x_pre >= (0 : Int))) (PreH2 : ((-10000) <= x_pre)) (PreH3 : (x_pre <= 10000)) ,
  TT && emp 
|--
  “ (x_pre = (Z.abs (x_pre))) ”
  &&  emp
) \/
(
forall (x_pre : Int) (PreH1 : (x_pre >= (0 : Int))) (PreH2 : ((-10000) <= x_pre)) (PreH3 : (x_pre <= 10000)) ,
  TT && emp 
|--
  “ (x_pre = (Z.abs (x_pre))) ”
  &&  emp
)

noncomputable def llabs_return_wit_2_split_goal_1 : Prop :=
  forall (x_pre : Int) (PreH1 : (x_pre >= (0 : Int))) (PreH2 : ((-10000) <= x_pre)) (PreH3 : (x_pre <= 10000)) ,
  (x_pre = (Z.abs (x_pre)))

noncomputable def gcdll_safety_wit_1 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (b : Int) (a : Int) (PreH1 : (1 <= a)) (PreH2 : (a <= 10000)) (PreH3 : ((0 : Int) <= b)) (PreH4 : (b <= 10000)) (PreH5 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH6 : (b ≠ (0 : Int))) ,
  ((( &( "r" ) )) # Int64 |->_)
  ** ((( &( "a" ) )) # Int64 |-> (a))
  ** ((( &( "b" ) )) # Int64 |-> (b))
|--
  “ ((a ≠ (-9223372036854775808)) ∨ (b ≠ (-1))) ” &&
  “ (b ≠ (0 : Int)) ”

noncomputable def gcdll_safety_wit_2 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (b : Int) (a : Int) (PreH1 : (1 <= a)) (PreH2 : (a <= 10000)) (PreH3 : ((0 : Int) <= b)) (PreH4 : (b <= 10000)) (PreH5 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH6 : (b = (0 : Int))) ,
  ((( &( "a" ) )) # Int64 |-> (a))
  ** ((( &( "b" ) )) # Int64 |-> (b))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def gcdll_safety_wit_3 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (b : Int) (a : Int) (PreH1 : (a < (0 : Int))) (PreH2 : (1 <= a)) (PreH3 : (a <= 10000)) (PreH4 : ((0 : Int) <= b)) (PreH5 : (b <= 10000)) (PreH6 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH7 : (b = (0 : Int))) ,
  ((( &( "a" ) )) # Int64 |-> (a))
  ** ((( &( "b" ) )) # Int64 |-> (b))
|--
  “ False ”

noncomputable def gcdll_entail_wit_1 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (PreH1 : (1 <= a_pre)) (PreH2 : (a_pre <= 10000)) (PreH3 : (1 <= b_pre)) (PreH4 : (b_pre <= 10000)) ,
  TT && emp 
|--
  “ (1 <= a_pre) ” &&
  “ (a_pre <= 10000) ” &&
  “ ((0 : Int) <= b_pre) ” &&
  “ (b_pre <= 10000) ” &&
  “ ((GcdValue (a_pre) (b_pre)) = (GcdValue (a_pre) (b_pre))) ”
  &&  emp

noncomputable def gcdll_entail_wit_2 : Prop :=
  (
forall (a_pre : Int) (b_pre : Int) (b : Int) (a : Int) (PreH1 : (1 <= a)) (PreH2 : (a <= 10000)) (PreH3 : ((0 : Int) <= b)) (PreH4 : (b <= 10000)) (PreH5 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH6 : (b ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (1 <= b) ” &&
  “ (b <= 10000) ” &&
  “ ((0 : Int) <= (Z.rem a b)) ” &&
  “ ((Z.rem a b) <= 10000) ” &&
  “ ((GcdValue (b) ((Z.rem a b))) = (GcdValue (a_pre) (b_pre))) ”
  &&  emp
) \/
(
forall (a_pre : Int) (b_pre : Int) (b : Int) (a : Int) (PreH1 : (1 <= a)) (PreH2 : (a <= 10000)) (PreH3 : ((0 : Int) <= b)) (PreH4 : (b <= 10000)) (PreH5 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH6 : (b ≠ (0 : Int))) ,
  TT && emp 
|--
  “ ((GcdValue (b) ((Z.rem a b))) = (GcdValue (a_pre) (b_pre))) ” &&
  “ ((Z.rem a b) <= 10000) ” &&
  “ ((0 : Int) <= (Z.rem a b)) ”
  &&  emp
)

noncomputable def gcdll_entail_wit_2_split_goal_1 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (b : Int) (a : Int) (PreH1 : (1 <= a)) (PreH2 : (a <= 10000)) (PreH3 : ((0 : Int) <= b)) (PreH4 : (b <= 10000)) (PreH5 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH6 : (b ≠ (0 : Int))) ,
  ((GcdValue (b) ((Z.rem a b))) = (GcdValue (a_pre) (b_pre)))

noncomputable def gcdll_entail_wit_2_split_goal_2 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (b : Int) (a : Int) (PreH1 : (1 <= a)) (PreH2 : (a <= 10000)) (PreH3 : ((0 : Int) <= b)) (PreH4 : (b <= 10000)) (PreH5 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH6 : (b ≠ (0 : Int))) ,
  ((Z.rem a b) <= 10000)

noncomputable def gcdll_entail_wit_2_split_goal_3 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (b : Int) (a : Int) (PreH1 : (1 <= a)) (PreH2 : (a <= 10000)) (PreH3 : ((0 : Int) <= b)) (PreH4 : (b <= 10000)) (PreH5 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH6 : (b ≠ (0 : Int))) ,
  ((0 : Int) <= (Z.rem a b))

noncomputable def gcdll_return_wit_1 : Prop :=
  (
forall (a_pre : Int) (b_pre : Int) (b : Int) (a : Int) (PreH1 : (a >= (0 : Int))) (PreH2 : (1 <= a)) (PreH3 : (a <= 10000)) (PreH4 : ((0 : Int) <= b)) (PreH5 : (b <= 10000)) (PreH6 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH7 : (b = (0 : Int))) ,
  TT && emp 
|--
  “ (a = (GcdValue (a_pre) (b_pre))) ”
  &&  emp
) \/
(
forall (a_pre : Int) (b_pre : Int) (b : Int) (a : Int) (PreH1 : (a >= (0 : Int))) (PreH2 : (1 <= a)) (PreH3 : (a <= 10000)) (PreH4 : ((0 : Int) <= b)) (PreH5 : (b <= 10000)) (PreH6 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH7 : (b = (0 : Int))) ,
  TT && emp 
|--
  “ (a = (GcdValue (a_pre) (b_pre))) ”
  &&  emp
)

noncomputable def gcdll_return_wit_1_split_goal_1 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (b : Int) (a : Int) (PreH1 : (a >= (0 : Int))) (PreH2 : (1 <= a)) (PreH3 : (a <= 10000)) (PreH4 : ((0 : Int) <= b)) (PreH5 : (b <= 10000)) (PreH6 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH7 : (b = (0 : Int))) ,
  (a = (GcdValue (a_pre) (b_pre)))

noncomputable def pair_fill_safety_wit_1 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (out_pre : Int) (retval : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 = (GcdValue (retval) (retval_2)))) (PreH2 : (retval_2 = (Z.abs (b_pre)))) (PreH3 : (retval = (Z.abs (a_pre)))) (PreH4 : ((-10000) <= a_pre)) (PreH5 : (a_pre <= 10000)) (PreH6 : (a_pre ≠ (0 : Int))) (PreH7 : ((-10000) <= b_pre)) (PreH8 : (b_pre <= 10000)) (PreH9 : (b_pre ≠ (0 : Int))) ,
  ((( &( "g" ) )) # Int64 |-> (retval_3))
  ** ((( &( "a" ) )) # Int64 |-> (a_pre))
  ** ((( &( "b" ) )) # Int64 |-> (b_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64Array.undef_full out_pre 2)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def pair_fill_safety_wit_2 : Prop :=
  (
forall (a_pre : Int) (b_pre : Int) (out_pre : Int) (retval_2 : Int) (retval_3 : Int) (retval : Int) (PreH1 : (retval = (GcdValue (retval_2) (retval_3)))) (PreH2 : (retval_3 = (Z.abs (b_pre)))) (PreH3 : (retval_2 = (Z.abs (a_pre)))) (PreH4 : ((-10000) <= a_pre)) (PreH5 : (a_pre <= 10000)) (PreH6 : (a_pre ≠ (0 : Int))) (PreH7 : ((-10000) <= b_pre)) (PreH8 : (b_pre <= 10000)) (PreH9 : (b_pre ≠ (0 : Int))) ,
  ((( &( "g" ) )) # Int64 |-> (retval))
  ** ((( &( "a" ) )) # Int64 |-> (a_pre))
  ** ((( &( "b" ) )) # Int64 |-> (b_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64Array.undef_full out_pre 2)
|--
  “ ((b_pre ≠ (-9223372036854775808)) ∨ (retval ≠ (-1))) ” &&
  “ (retval ≠ (0 : Int)) ”
) \/
(
forall (a_pre : Int) (b_pre : Int) (out_pre : Int) (retval_2 : Int) (retval_3 : Int) (retval : Int) (PreH1 : (retval = (GcdValue (retval_2) (retval_3)))) (PreH2 : (retval_3 = (Z.abs (b_pre)))) (PreH3 : (retval_2 = (Z.abs (a_pre)))) (PreH4 : ((-10000) <= a_pre)) (PreH5 : (a_pre <= 10000)) (PreH6 : (a_pre ≠ (0 : Int))) (PreH7 : ((-10000) <= b_pre)) (PreH8 : (b_pre <= 10000)) (PreH9 : (b_pre ≠ (0 : Int))) ,
  ((( &( "g" ) )) # Int64 |-> (retval))
  ** ((( &( "a" ) )) # Int64 |-> (a_pre))
  ** ((( &( "b" ) )) # Int64 |-> (b_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64Array.undef_full out_pre 2)
|--
  “ ((b_pre ≠ (-9223372036854775808)) ∨ (retval ≠ (-1))) ” &&
  “ (retval ≠ (0 : Int)) ”
)

noncomputable def pair_fill_safety_wit_2_split_goal_1 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (out_pre : Int) (retval_2 : Int) (retval_3 : Int) (retval : Int) (PreH1 : (retval = (GcdValue (retval_2) (retval_3)))) (PreH2 : (retval_3 = (Z.abs (b_pre)))) (PreH3 : (retval_2 = (Z.abs (a_pre)))) (PreH4 : ((-10000) <= a_pre)) (PreH5 : (a_pre <= 10000)) (PreH6 : (a_pre ≠ (0 : Int))) (PreH7 : ((-10000) <= b_pre)) (PreH8 : (b_pre <= 10000)) (PreH9 : (b_pre ≠ (0 : Int))) ,
  ((( &( "g" ) )) # Int64 |-> (retval))
  ** ((( &( "a" ) )) # Int64 |-> (a_pre))
  ** ((( &( "b" ) )) # Int64 |-> (b_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64Array.undef_full out_pre 2)
|--
  “ ((b_pre ≠ (-9223372036854775808)) ∨ (retval ≠ (-1))) ”

noncomputable def pair_fill_safety_wit_2_split_goal_2 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (out_pre : Int) (retval_2 : Int) (retval_3 : Int) (retval : Int) (PreH1 : (retval = (GcdValue (retval_2) (retval_3)))) (PreH2 : (retval_3 = (Z.abs (b_pre)))) (PreH3 : (retval_2 = (Z.abs (a_pre)))) (PreH4 : ((-10000) <= a_pre)) (PreH5 : (a_pre <= 10000)) (PreH6 : (a_pre ≠ (0 : Int))) (PreH7 : ((-10000) <= b_pre)) (PreH8 : (b_pre <= 10000)) (PreH9 : (b_pre ≠ (0 : Int))) ,
  ((( &( "g" ) )) # Int64 |-> (retval))
  ** ((( &( "a" ) )) # Int64 |-> (a_pre))
  ** ((( &( "b" ) )) # Int64 |-> (b_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64Array.undef_full out_pre 2)
|--
  “ (retval ≠ (0 : Int)) ”

noncomputable def pair_fill_safety_wit_3 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (out_pre : Int) (retval : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 = (GcdValue (retval) (retval_2)))) (PreH2 : (retval_2 = (Z.abs (b_pre)))) (PreH3 : (retval = (Z.abs (a_pre)))) (PreH4 : ((-10000) <= a_pre)) (PreH5 : (a_pre <= 10000)) (PreH6 : (a_pre ≠ (0 : Int))) (PreH7 : ((-10000) <= b_pre)) (PreH8 : (b_pre <= 10000)) (PreH9 : (b_pre ≠ (0 : Int))) ,
  (((out_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> ((Z.quot b_pre retval_3)))
  ** (int64Array.undef_seg out_pre 1 2)
  ** ((( &( "g" ) )) # Int64 |-> (retval_3))
  ** ((( &( "a" ) )) # Int64 |-> (a_pre))
  ** ((( &( "b" ) )) # Int64 |-> (b_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def pair_fill_safety_wit_4 : Prop :=
  (
forall (a_pre : Int) (b_pre : Int) (out_pre : Int) (retval_2 : Int) (retval_3 : Int) (retval : Int) (PreH1 : (retval = (GcdValue (retval_2) (retval_3)))) (PreH2 : (retval_3 = (Z.abs (b_pre)))) (PreH3 : (retval_2 = (Z.abs (a_pre)))) (PreH4 : ((-10000) <= a_pre)) (PreH5 : (a_pre <= 10000)) (PreH6 : (a_pre ≠ (0 : Int))) (PreH7 : ((-10000) <= b_pre)) (PreH8 : (b_pre <= 10000)) (PreH9 : (b_pre ≠ (0 : Int))) ,
  (((out_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> ((Z.quot b_pre retval)))
  ** (int64Array.undef_seg out_pre 1 2)
  ** ((( &( "g" ) )) # Int64 |-> (retval))
  ** ((( &( "a" ) )) # Int64 |-> (a_pre))
  ** ((( &( "b" ) )) # Int64 |-> (b_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
|--
  “ (((-a_pre) ≠ (-9223372036854775808)) ∨ (retval ≠ (-1))) ” &&
  “ (retval ≠ (0 : Int)) ”
) \/
(
forall (a_pre : Int) (b_pre : Int) (out_pre : Int) (retval_2 : Int) (retval_3 : Int) (retval : Int) (PreH1 : (retval = (GcdValue (retval_2) (retval_3)))) (PreH2 : (retval_3 = (Z.abs (b_pre)))) (PreH3 : (retval_2 = (Z.abs (a_pre)))) (PreH4 : ((-10000) <= a_pre)) (PreH5 : (a_pre <= 10000)) (PreH6 : (a_pre ≠ (0 : Int))) (PreH7 : ((-10000) <= b_pre)) (PreH8 : (b_pre <= 10000)) (PreH9 : (b_pre ≠ (0 : Int))) ,
  (((out_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> ((Z.quot b_pre retval)))
  ** (int64Array.undef_seg out_pre 1 2)
  ** ((( &( "g" ) )) # Int64 |-> (retval))
  ** ((( &( "a" ) )) # Int64 |-> (a_pre))
  ** ((( &( "b" ) )) # Int64 |-> (b_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
|--
  “ (((-a_pre) ≠ (-9223372036854775808)) ∨ (retval ≠ (-1))) ” &&
  “ (retval ≠ (0 : Int)) ”
)

noncomputable def pair_fill_safety_wit_4_split_goal_1 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (out_pre : Int) (retval_2 : Int) (retval_3 : Int) (retval : Int) (PreH1 : (retval = (GcdValue (retval_2) (retval_3)))) (PreH2 : (retval_3 = (Z.abs (b_pre)))) (PreH3 : (retval_2 = (Z.abs (a_pre)))) (PreH4 : ((-10000) <= a_pre)) (PreH5 : (a_pre <= 10000)) (PreH6 : (a_pre ≠ (0 : Int))) (PreH7 : ((-10000) <= b_pre)) (PreH8 : (b_pre <= 10000)) (PreH9 : (b_pre ≠ (0 : Int))) ,
  (((out_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> ((Z.quot b_pre retval)))
  ** (int64Array.undef_seg out_pre 1 2)
  ** ((( &( "g" ) )) # Int64 |-> (retval))
  ** ((( &( "a" ) )) # Int64 |-> (a_pre))
  ** ((( &( "b" ) )) # Int64 |-> (b_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
|--
  “ (((-a_pre) ≠ (-9223372036854775808)) ∨ (retval ≠ (-1))) ”

noncomputable def pair_fill_safety_wit_4_split_goal_2 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (out_pre : Int) (retval_2 : Int) (retval_3 : Int) (retval : Int) (PreH1 : (retval = (GcdValue (retval_2) (retval_3)))) (PreH2 : (retval_3 = (Z.abs (b_pre)))) (PreH3 : (retval_2 = (Z.abs (a_pre)))) (PreH4 : ((-10000) <= a_pre)) (PreH5 : (a_pre <= 10000)) (PreH6 : (a_pre ≠ (0 : Int))) (PreH7 : ((-10000) <= b_pre)) (PreH8 : (b_pre <= 10000)) (PreH9 : (b_pre ≠ (0 : Int))) ,
  (((out_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> ((Z.quot b_pre retval)))
  ** (int64Array.undef_seg out_pre 1 2)
  ** ((( &( "g" ) )) # Int64 |-> (retval))
  ** ((( &( "a" ) )) # Int64 |-> (a_pre))
  ** ((( &( "b" ) )) # Int64 |-> (b_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
|--
  “ (retval ≠ (0 : Int)) ”

noncomputable def pair_fill_safety_wit_5 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (out_pre : Int) (retval : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 = (GcdValue (retval) (retval_2)))) (PreH2 : (retval_2 = (Z.abs (b_pre)))) (PreH3 : (retval = (Z.abs (a_pre)))) (PreH4 : ((-10000) <= a_pre)) (PreH5 : (a_pre <= 10000)) (PreH6 : (a_pre ≠ (0 : Int))) (PreH7 : ((-10000) <= b_pre)) (PreH8 : (b_pre <= 10000)) (PreH9 : (b_pre ≠ (0 : Int))) ,
  (((out_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> ((Z.quot b_pre retval_3)))
  ** (int64Array.undef_seg out_pre 1 2)
  ** ((( &( "g" ) )) # Int64 |-> (retval_3))
  ** ((( &( "a" ) )) # Int64 |-> (a_pre))
  ** ((( &( "b" ) )) # Int64 |-> (b_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
|--
  “ (a_pre ≠ (-9223372036854775808)) ”

noncomputable def pair_fill_return_wit_1 : Prop :=
  (
forall (a_pre : Int) (b_pre : Int) (out_pre : Int) (retval : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 = (GcdValue (retval) (retval_2)))) (PreH2 : (retval_2 = (Z.abs (b_pre)))) (PreH3 : (retval = (Z.abs (a_pre)))) (PreH4 : ((-10000) <= a_pre)) (PreH5 : (a_pre <= 10000)) (PreH6 : (a_pre ≠ (0 : Int))) (PreH7 : ((-10000) <= b_pre)) (PreH8 : (b_pre <= 10000)) (PreH9 : (b_pre ≠ (0 : Int))) ,
  (((out_pre + (1 * sizeof(INT64)))) # Int64 |-> ((Z.quot (-a_pre) retval_3)))
  ** (((out_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> ((Z.quot b_pre retval_3)))
|--
  EX pair_out : (List Int),
  “ (OutputPrefix (a_pre :: (b_pre :: (@List.nil Int))) pair_out (0 : Int)) ”
  &&  (int64Array.full out_pre 2 pair_out)
) \/
(
forall (a_pre : Int) (b_pre : Int) (out_pre : Int) (retval : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : ((Z.quot b_pre retval_3) <= 9223372036854775807)) (PreH2 : ((Z.quot (-a_pre) retval_3) <= 9223372036854775807)) (PreH3 : ((Z.quot b_pre retval_3) >= (-9223372036854775808))) (PreH4 : ((Z.quot (-a_pre) retval_3) >= (-9223372036854775808))) (PreH5 : (retval_3 = (GcdValue (retval) (retval_2)))) (PreH6 : (retval_2 = (Z.abs (b_pre)))) (PreH7 : (retval = (Z.abs (a_pre)))) (PreH8 : ((-10000) <= a_pre)) (PreH9 : (a_pre <= 10000)) (PreH10 : (a_pre ≠ (0 : Int))) (PreH11 : ((-10000) <= b_pre)) (PreH12 : (b_pre <= 10000)) (PreH13 : (b_pre ≠ (0 : Int))) ,
  (((out_pre + (1 * sizeof(INT64)))) # Int64 |-> ((Z.quot (-a_pre) retval_3)))
  ** (((out_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> ((Z.quot b_pre retval_3)))
|--
  EX pair_out : (List Int),
  “ (OutputPrefix (a_pre :: (b_pre :: (@List.nil Int))) pair_out (0 : Int)) ”
  &&  (int64Array.full out_pre 2 pair_out)
)

noncomputable def pair_fill_partial_solve_wit_1_pure : Prop :=
  forall (a_pre : Int) (b_pre : Int) (out_pre : Int) (PreH1 : ((-10000) <= a_pre)) (PreH2 : (a_pre <= 10000)) (PreH3 : (a_pre ≠ (0 : Int))) (PreH4 : ((-10000) <= b_pre)) (PreH5 : (b_pre <= 10000)) (PreH6 : (b_pre ≠ (0 : Int))) ,
  ((( &( "g" ) )) # Int64 |->_)
  ** ((( &( "a" ) )) # Int64 |-> (a_pre))
  ** ((( &( "b" ) )) # Int64 |-> (b_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64Array.undef_full out_pre 2)
|--
  “ ((-10000) <= a_pre) ” &&
  “ (a_pre <= 10000) ”

noncomputable def pair_fill_partial_solve_wit_1_aux : Prop :=
  forall (a_pre : Int) (b_pre : Int) (out_pre : Int) (PreH1 : ((-10000) <= a_pre)) (PreH2 : (a_pre <= 10000)) (PreH3 : (a_pre ≠ (0 : Int))) (PreH4 : ((-10000) <= b_pre)) (PreH5 : (b_pre <= 10000)) (PreH6 : (b_pre ≠ (0 : Int))) ,
  (int64Array.undef_full out_pre 2)
|--
  “ ((-10000) <= a_pre) ” &&
  “ (a_pre <= 10000) ” &&
  “ ((-10000) <= a_pre) ” &&
  “ (a_pre <= 10000) ” &&
  “ (a_pre ≠ (0 : Int)) ” &&
  “ ((-10000) <= b_pre) ” &&
  “ (b_pre <= 10000) ” &&
  “ (b_pre ≠ (0 : Int)) ”
  &&  (int64Array.undef_full out_pre 2)

noncomputable def pair_fill_partial_solve_wit_1 : Prop := pair_fill_partial_solve_wit_1_pure -> pair_fill_partial_solve_wit_1_aux

noncomputable def pair_fill_partial_solve_wit_2_pure : Prop :=
  forall (a_pre : Int) (b_pre : Int) (out_pre : Int) (retval : Int) (PreH1 : (retval = (Z.abs (a_pre)))) (PreH2 : ((-10000) <= a_pre)) (PreH3 : (a_pre <= 10000)) (PreH4 : (a_pre ≠ (0 : Int))) (PreH5 : ((-10000) <= b_pre)) (PreH6 : (b_pre <= 10000)) (PreH7 : (b_pre ≠ (0 : Int))) ,
  ((( &( "g" ) )) # Int64 |->_)
  ** ((( &( "a" ) )) # Int64 |-> (a_pre))
  ** ((( &( "b" ) )) # Int64 |-> (b_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64Array.undef_full out_pre 2)
|--
  “ ((-10000) <= b_pre) ” &&
  “ (b_pre <= 10000) ”

noncomputable def pair_fill_partial_solve_wit_2_aux : Prop :=
  forall (a_pre : Int) (b_pre : Int) (out_pre : Int) (retval : Int) (PreH1 : (retval = (Z.abs (a_pre)))) (PreH2 : ((-10000) <= a_pre)) (PreH3 : (a_pre <= 10000)) (PreH4 : (a_pre ≠ (0 : Int))) (PreH5 : ((-10000) <= b_pre)) (PreH6 : (b_pre <= 10000)) (PreH7 : (b_pre ≠ (0 : Int))) ,
  (int64Array.undef_full out_pre 2)
|--
  “ ((-10000) <= b_pre) ” &&
  “ (b_pre <= 10000) ” &&
  “ (retval = (Z.abs (a_pre))) ” &&
  “ ((-10000) <= a_pre) ” &&
  “ (a_pre <= 10000) ” &&
  “ (a_pre ≠ (0 : Int)) ” &&
  “ ((-10000) <= b_pre) ” &&
  “ (b_pre <= 10000) ” &&
  “ (b_pre ≠ (0 : Int)) ”
  &&  (int64Array.undef_full out_pre 2)

noncomputable def pair_fill_partial_solve_wit_2 : Prop := pair_fill_partial_solve_wit_2_pure -> pair_fill_partial_solve_wit_2_aux

noncomputable def pair_fill_partial_solve_wit_3_pure : Prop :=
  (
forall (a_pre : Int) (b_pre : Int) (out_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (Z.abs (b_pre)))) (PreH2 : (retval = (Z.abs (a_pre)))) (PreH3 : ((-10000) <= a_pre)) (PreH4 : (a_pre <= 10000)) (PreH5 : (a_pre ≠ (0 : Int))) (PreH6 : ((-10000) <= b_pre)) (PreH7 : (b_pre <= 10000)) (PreH8 : (b_pre ≠ (0 : Int))) ,
  ((( &( "g" ) )) # Int64 |->_)
  ** ((( &( "a" ) )) # Int64 |-> (a_pre))
  ** ((( &( "b" ) )) # Int64 |-> (b_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64Array.undef_full out_pre 2)
|--
  “ (retval_2 <= 10000) ” &&
  “ (1 <= retval_2) ” &&
  “ (retval <= 10000) ” &&
  “ (1 <= retval) ”
) \/
(
forall (a_pre : Int) (b_pre : Int) (out_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (b_pre <= 9223372036854775807)) (PreH2 : (a_pre <= 9223372036854775807)) (PreH3 : (b_pre >= (-9223372036854775808))) (PreH4 : (a_pre >= (-9223372036854775808))) (PreH5 : (retval_2 = (Z.abs (b_pre)))) (PreH6 : (retval = (Z.abs (a_pre)))) (PreH7 : ((-10000) <= a_pre)) (PreH8 : (a_pre <= 10000)) (PreH9 : (a_pre ≠ (0 : Int))) (PreH10 : ((-10000) <= b_pre)) (PreH11 : (b_pre <= 10000)) (PreH12 : (b_pre ≠ (0 : Int))) ,
  ((( &( "g" ) )) # Int64 |->_)
  ** ((( &( "a" ) )) # Int64 |-> (a_pre))
  ** ((( &( "b" ) )) # Int64 |-> (b_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64Array.undef_full out_pre 2)
|--
  “ (1 <= retval) ” &&
  “ (retval <= 10000) ” &&
  “ (1 <= retval_2) ” &&
  “ (retval_2 <= 10000) ”
)

noncomputable def pair_fill_partial_solve_wit_3_pure_split_goal_1 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (out_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (b_pre <= 9223372036854775807)) (PreH2 : (a_pre <= 9223372036854775807)) (PreH3 : (b_pre >= (-9223372036854775808))) (PreH4 : (a_pre >= (-9223372036854775808))) (PreH5 : (retval_2 = (Z.abs (b_pre)))) (PreH6 : (retval = (Z.abs (a_pre)))) (PreH7 : ((-10000) <= a_pre)) (PreH8 : (a_pre <= 10000)) (PreH9 : (a_pre ≠ (0 : Int))) (PreH10 : ((-10000) <= b_pre)) (PreH11 : (b_pre <= 10000)) (PreH12 : (b_pre ≠ (0 : Int))) ,
  ((( &( "g" ) )) # Int64 |->_)
  ** ((( &( "a" ) )) # Int64 |-> (a_pre))
  ** ((( &( "b" ) )) # Int64 |-> (b_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64Array.undef_full out_pre 2)
|--
  “ (1 <= retval) ”

noncomputable def pair_fill_partial_solve_wit_3_pure_split_goal_2 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (out_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (b_pre <= 9223372036854775807)) (PreH2 : (a_pre <= 9223372036854775807)) (PreH3 : (b_pre >= (-9223372036854775808))) (PreH4 : (a_pre >= (-9223372036854775808))) (PreH5 : (retval_2 = (Z.abs (b_pre)))) (PreH6 : (retval = (Z.abs (a_pre)))) (PreH7 : ((-10000) <= a_pre)) (PreH8 : (a_pre <= 10000)) (PreH9 : (a_pre ≠ (0 : Int))) (PreH10 : ((-10000) <= b_pre)) (PreH11 : (b_pre <= 10000)) (PreH12 : (b_pre ≠ (0 : Int))) ,
  ((( &( "g" ) )) # Int64 |->_)
  ** ((( &( "a" ) )) # Int64 |-> (a_pre))
  ** ((( &( "b" ) )) # Int64 |-> (b_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64Array.undef_full out_pre 2)
|--
  “ (retval <= 10000) ”

noncomputable def pair_fill_partial_solve_wit_3_pure_split_goal_3 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (out_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (b_pre <= 9223372036854775807)) (PreH2 : (a_pre <= 9223372036854775807)) (PreH3 : (b_pre >= (-9223372036854775808))) (PreH4 : (a_pre >= (-9223372036854775808))) (PreH5 : (retval_2 = (Z.abs (b_pre)))) (PreH6 : (retval = (Z.abs (a_pre)))) (PreH7 : ((-10000) <= a_pre)) (PreH8 : (a_pre <= 10000)) (PreH9 : (a_pre ≠ (0 : Int))) (PreH10 : ((-10000) <= b_pre)) (PreH11 : (b_pre <= 10000)) (PreH12 : (b_pre ≠ (0 : Int))) ,
  ((( &( "g" ) )) # Int64 |->_)
  ** ((( &( "a" ) )) # Int64 |-> (a_pre))
  ** ((( &( "b" ) )) # Int64 |-> (b_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64Array.undef_full out_pre 2)
|--
  “ (1 <= retval_2) ”

noncomputable def pair_fill_partial_solve_wit_3_pure_split_goal_4 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (out_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (b_pre <= 9223372036854775807)) (PreH2 : (a_pre <= 9223372036854775807)) (PreH3 : (b_pre >= (-9223372036854775808))) (PreH4 : (a_pre >= (-9223372036854775808))) (PreH5 : (retval_2 = (Z.abs (b_pre)))) (PreH6 : (retval = (Z.abs (a_pre)))) (PreH7 : ((-10000) <= a_pre)) (PreH8 : (a_pre <= 10000)) (PreH9 : (a_pre ≠ (0 : Int))) (PreH10 : ((-10000) <= b_pre)) (PreH11 : (b_pre <= 10000)) (PreH12 : (b_pre ≠ (0 : Int))) ,
  ((( &( "g" ) )) # Int64 |->_)
  ** ((( &( "a" ) )) # Int64 |-> (a_pre))
  ** ((( &( "b" ) )) # Int64 |-> (b_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64Array.undef_full out_pre 2)
|--
  “ (retval_2 <= 10000) ”

noncomputable def pair_fill_partial_solve_wit_3_aux : Prop :=
  forall (a_pre : Int) (b_pre : Int) (out_pre : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (Z.abs (b_pre)))) (PreH2 : (retval = (Z.abs (a_pre)))) (PreH3 : ((-10000) <= a_pre)) (PreH4 : (a_pre <= 10000)) (PreH5 : (a_pre ≠ (0 : Int))) (PreH6 : ((-10000) <= b_pre)) (PreH7 : (b_pre <= 10000)) (PreH8 : (b_pre ≠ (0 : Int))) ,
  (int64Array.undef_full out_pre 2)
|--
  “ (retval_2 <= 10000) ” &&
  “ (1 <= retval_2) ” &&
  “ (retval <= 10000) ” &&
  “ (1 <= retval) ” &&
  “ (retval_2 = (Z.abs (b_pre))) ” &&
  “ (retval = (Z.abs (a_pre))) ” &&
  “ ((-10000) <= a_pre) ” &&
  “ (a_pre <= 10000) ” &&
  “ (a_pre ≠ (0 : Int)) ” &&
  “ ((-10000) <= b_pre) ” &&
  “ (b_pre <= 10000) ” &&
  “ (b_pre ≠ (0 : Int)) ”
  &&  (int64Array.undef_full out_pre 2)

noncomputable def pair_fill_partial_solve_wit_3 : Prop := pair_fill_partial_solve_wit_3_pure -> pair_fill_partial_solve_wit_3_aux

noncomputable def pair_fill_partial_solve_wit_4 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (out_pre : Int) (retval : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 = (GcdValue (retval) (retval_2)))) (PreH2 : (retval_2 = (Z.abs (b_pre)))) (PreH3 : (retval = (Z.abs (a_pre)))) (PreH4 : ((-10000) <= a_pre)) (PreH5 : (a_pre <= 10000)) (PreH6 : (a_pre ≠ (0 : Int))) (PreH7 : ((-10000) <= b_pre)) (PreH8 : (b_pre <= 10000)) (PreH9 : (b_pre ≠ (0 : Int))) ,
  (int64Array.undef_full out_pre 2)
|--
  “ (retval_3 = (GcdValue (retval) (retval_2))) ” &&
  “ (retval_2 = (Z.abs (b_pre))) ” &&
  “ (retval = (Z.abs (a_pre))) ” &&
  “ ((-10000) <= a_pre) ” &&
  “ (a_pre <= 10000) ” &&
  “ (a_pre ≠ (0 : Int)) ” &&
  “ ((-10000) <= b_pre) ” &&
  “ (b_pre <= 10000) ” &&
  “ (b_pre ≠ (0 : Int)) ”
  &&  (((out_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |->_)
  ** (int64Array.undef_seg out_pre 1 2)

noncomputable def pair_fill_partial_solve_wit_5 : Prop :=
  forall (a_pre : Int) (b_pre : Int) (out_pre : Int) (retval : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 = (GcdValue (retval) (retval_2)))) (PreH2 : (retval_2 = (Z.abs (b_pre)))) (PreH3 : (retval = (Z.abs (a_pre)))) (PreH4 : ((-10000) <= a_pre)) (PreH5 : (a_pre <= 10000)) (PreH6 : (a_pre ≠ (0 : Int))) (PreH7 : ((-10000) <= b_pre)) (PreH8 : (b_pre <= 10000)) (PreH9 : (b_pre ≠ (0 : Int))) ,
  (((out_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> ((Z.quot b_pre retval_3)))
  ** (int64Array.undef_seg out_pre 1 2)
|--
  “ (retval_3 = (GcdValue (retval) (retval_2))) ” &&
  “ (retval_2 = (Z.abs (b_pre))) ” &&
  “ (retval = (Z.abs (a_pre))) ” &&
  “ ((-10000) <= a_pre) ” &&
  “ (a_pre <= 10000) ” &&
  “ (a_pre ≠ (0 : Int)) ” &&
  “ ((-10000) <= b_pre) ” &&
  “ (b_pre <= 10000) ” &&
  “ (b_pre ≠ (0 : Int)) ”
  &&  (((out_pre + (1 * sizeof(INT64)))) # Int64 |->_)
  ** (((out_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> ((Z.quot b_pre retval_3)))

noncomputable def solver_safety_wit_1 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH4 : (n_pre = (Zlength (values)))) ,
  ((( &( "start" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** (intArray.full a_pre n_pre values)
  ** (int64Array.undef_full b_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH4 : (n_pre = (Zlength (values)))) ,
  ((( &( "start" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** (intArray.full a_pre n_pre values)
  ** (int64Array.undef_full b_pre n_pre)
|--
  “ ((n_pre ≠ (INT_MIN)) ∨ (2 ≠ (-1))) ” &&
  “ (2 ≠ (0 : Int)) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH4 : (n_pre = (Zlength (values)))) ,
  ((( &( "start" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** (intArray.full a_pre n_pre values)
  ** (int64Array.undef_full b_pre n_pre)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (3 <= n_pre)) (PreH2 : ((0 : Int) <= INT_MAX)) (PreH3 : ((0 : Int) >= INT_MIN)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  ((( &( "z" ) )) # Int64 |->_)
  ** (intArray.full a_pre n_pre values)
  ** ((( &( "y" ) )) # Int64 |-> ((Znth 1 values (0 : Int))))
  ** ((( &( "x" ) )) # Int64 |-> ((Znth (0 : Int) values (0 : Int))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "start" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** (int64Array.undef_full b_pre n_pre)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (3 <= n_pre)) (PreH2 : ((0 : Int) <= INT_MAX)) (PreH3 : ((0 : Int) >= INT_MIN)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  ((( &( "y" ) )) # Int64 |->_)
  ** (intArray.full a_pre n_pre values)
  ** ((( &( "x" ) )) # Int64 |-> ((Znth (0 : Int) values (0 : Int))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "start" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** (int64Array.undef_full b_pre n_pre)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (3 <= n_pre)) (PreH2 : ((0 : Int) <= INT_MAX)) (PreH3 : ((0 : Int) >= INT_MIN)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  ((( &( "x" ) )) # Int64 |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "start" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** (intArray.full a_pre n_pre values)
  ** (int64Array.undef_full b_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_7 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (3 <= n_pre)) (PreH2 : ((0 : Int) <= INT_MAX)) (PreH3 : ((0 : Int) >= INT_MIN)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "z" ) )) # Int64 |-> ((Znth 2 values (0 : Int))))
  ** ((( &( "y" ) )) # Int64 |-> ((Znth 1 values (0 : Int))))
  ** ((( &( "x" ) )) # Int64 |-> ((Znth (0 : Int) values (0 : Int))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "start" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** (int64Array.undef_full b_pre n_pre)
|--
  “ (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int)))) ”

noncomputable def solver_safety_wit_8 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (3 <= n_pre)) (PreH2 : ((0 : Int) <= INT_MAX)) (PreH3 : ((0 : Int) >= INT_MIN)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "z" ) )) # Int64 |-> ((Znth 2 values (0 : Int))))
  ** ((( &( "y" ) )) # Int64 |-> ((Znth 1 values (0 : Int))))
  ** ((( &( "x" ) )) # Int64 |-> ((Znth (0 : Int) values (0 : Int))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "start" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** (int64Array.undef_full b_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_9 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) ≠ (0 : Int))) (PreH2 : (3 <= n_pre)) (PreH3 : ((0 : Int) <= INT_MAX)) (PreH4 : ((0 : Int) >= INT_MIN)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "z" ) )) # Int64 |-> ((Znth 2 values (0 : Int))))
  ** ((( &( "y" ) )) # Int64 |-> ((Znth 1 values (0 : Int))))
  ** ((( &( "x" ) )) # Int64 |-> ((Znth (0 : Int) values (0 : Int))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "start" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** (int64Array.undef_full b_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_10 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) ≠ (0 : Int))) (PreH2 : (3 <= n_pre)) (PreH3 : ((0 : Int) <= INT_MAX)) (PreH4 : ((0 : Int) >= INT_MIN)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (((b_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> ((Znth 2 values (0 : Int))))
  ** (int64Array.undef_seg b_pre 1 n_pre)
  ** (intArray.full a_pre n_pre values)
  ** ((( &( "z" ) )) # Int64 |-> ((Znth 2 values (0 : Int))))
  ** ((( &( "y" ) )) # Int64 |-> ((Znth 1 values (0 : Int))))
  ** ((( &( "x" ) )) # Int64 |-> ((Znth (0 : Int) values (0 : Int))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "start" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_11 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) ≠ (0 : Int))) (PreH2 : (3 <= n_pre)) (PreH3 : ((0 : Int) <= INT_MAX)) (PreH4 : ((0 : Int) >= INT_MIN)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (((b_pre + (1 * sizeof(INT64)))) # Int64 |-> ((Znth 2 values (0 : Int))))
  ** (int64Array.undef_seg b_pre (1 + 1) n_pre)
  ** (((b_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> ((Znth 2 values (0 : Int))))
  ** (intArray.full a_pre n_pre values)
  ** ((( &( "z" ) )) # Int64 |-> ((Znth 2 values (0 : Int))))
  ** ((( &( "y" ) )) # Int64 |-> ((Znth 1 values (0 : Int))))
  ** ((( &( "x" ) )) # Int64 |-> ((Znth (0 : Int) values (0 : Int))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "start" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_12 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) ≠ (0 : Int))) (PreH2 : (3 <= n_pre)) (PreH3 : ((0 : Int) <= INT_MAX)) (PreH4 : ((0 : Int) >= INT_MIN)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (((b_pre + (1 * sizeof(INT64)))) # Int64 |-> ((Znth 2 values (0 : Int))))
  ** (int64Array.undef_seg b_pre (1 + 1) n_pre)
  ** (((b_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> ((Znth 2 values (0 : Int))))
  ** (intArray.full a_pre n_pre values)
  ** ((( &( "z" ) )) # Int64 |-> ((Znth 2 values (0 : Int))))
  ** ((( &( "y" ) )) # Int64 |-> ((Znth 1 values (0 : Int))))
  ** ((( &( "x" ) )) # Int64 |-> ((Znth (0 : Int) values (0 : Int))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "start" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
|--
  “ (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) ≠ (-9223372036854775808)) ”

noncomputable def solver_safety_wit_13 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) ≠ (0 : Int))) (PreH2 : (3 <= n_pre)) (PreH3 : ((0 : Int) <= INT_MAX)) (PreH4 : ((0 : Int) >= INT_MIN)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (((b_pre + (1 * sizeof(INT64)))) # Int64 |-> ((Znth 2 values (0 : Int))))
  ** (int64Array.undef_seg b_pre (1 + 1) n_pre)
  ** (((b_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> ((Znth 2 values (0 : Int))))
  ** (intArray.full a_pre n_pre values)
  ** ((( &( "z" ) )) # Int64 |-> ((Znth 2 values (0 : Int))))
  ** ((( &( "y" ) )) # Int64 |-> ((Znth 1 values (0 : Int))))
  ** ((( &( "x" ) )) # Int64 |-> ((Znth (0 : Int) values (0 : Int))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "start" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
|--
  “ (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int)))) ”

noncomputable def solver_safety_wit_14 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) = (0 : Int))) (PreH2 : (3 <= n_pre)) (PreH3 : ((0 : Int) <= INT_MAX)) (PreH4 : ((0 : Int) >= INT_MIN)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "z" ) )) # Int64 |-> ((Znth 2 values (0 : Int))))
  ** ((( &( "y" ) )) # Int64 |-> ((Znth 1 values (0 : Int))))
  ** ((( &( "x" ) )) # Int64 |-> ((Znth (0 : Int) values (0 : Int))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "start" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** (int64Array.undef_full b_pre n_pre)
|--
  “ (((Znth (0 : Int) values (0 : Int)) + (Znth 2 values (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((Znth (0 : Int) values (0 : Int)) + (Znth 2 values (0 : Int)))) ”

noncomputable def solver_safety_wit_15 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) = (0 : Int))) (PreH2 : (3 <= n_pre)) (PreH3 : ((0 : Int) <= INT_MAX)) (PreH4 : ((0 : Int) >= INT_MIN)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "z" ) )) # Int64 |-> ((Znth 2 values (0 : Int))))
  ** ((( &( "y" ) )) # Int64 |-> ((Znth 1 values (0 : Int))))
  ** ((( &( "x" ) )) # Int64 |-> ((Znth (0 : Int) values (0 : Int))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "start" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** (int64Array.undef_full b_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_16 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (((Znth (0 : Int) values (0 : Int)) + (Znth 2 values (0 : Int))) ≠ (0 : Int))) (PreH2 : (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) = (0 : Int))) (PreH3 : (3 <= n_pre)) (PreH4 : ((0 : Int) <= INT_MAX)) (PreH5 : ((0 : Int) >= INT_MIN)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "z" ) )) # Int64 |-> ((Znth 2 values (0 : Int))))
  ** ((( &( "y" ) )) # Int64 |-> ((Znth 1 values (0 : Int))))
  ** ((( &( "x" ) )) # Int64 |-> ((Znth (0 : Int) values (0 : Int))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "start" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** (int64Array.undef_full b_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_17 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (((Znth (0 : Int) values (0 : Int)) + (Znth 2 values (0 : Int))) ≠ (0 : Int))) (PreH2 : (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) = (0 : Int))) (PreH3 : (3 <= n_pre)) (PreH4 : ((0 : Int) <= INT_MAX)) (PreH5 : ((0 : Int) >= INT_MIN)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (((b_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> ((Znth 1 values (0 : Int))))
  ** (int64Array.undef_seg b_pre 1 n_pre)
  ** (intArray.full a_pre n_pre values)
  ** ((( &( "z" ) )) # Int64 |-> ((Znth 2 values (0 : Int))))
  ** ((( &( "y" ) )) # Int64 |-> ((Znth 1 values (0 : Int))))
  ** ((( &( "x" ) )) # Int64 |-> ((Znth (0 : Int) values (0 : Int))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "start" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_18 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (start : Int) (x : Int) (y : Int) (z : Int) (PreH1 : (start = (0 : Int))) (PreH2 : (3 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Z.rem n_pre 2) ≠ (0 : Int))) (PreH6 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int))))) (PreH7 : (x = (Znth (0 : Int) values (0 : Int)))) (PreH8 : (y = (Znth 1 values (0 : Int)))) (PreH9 : (z = (Znth 2 values (0 : Int)))) (PreH10 : ((x + y) = (0 : Int))) (PreH11 : ((x + z) ≠ (0 : Int))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "x" ) )) # Int64 |-> (x))
  ** ((( &( "y" ) )) # Int64 |-> (y))
  ** ((( &( "z" ) )) # Int64 |-> (z))
  ** (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) 1 (y :: (@List.nil Int)))
  ** (int64Array.undef_seg b_pre 1 2)
  ** (int64Array.seg b_pre 2 3 (y :: (@List.nil Int)))
  ** (int64Array.undef_seg b_pre 3 n_pre)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_19 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (start : Int) (x : Int) (y : Int) (z : Int) (PreH1 : (start = (0 : Int))) (PreH2 : (3 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Z.rem n_pre 2) ≠ (0 : Int))) (PreH6 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int))))) (PreH7 : (x = (Znth (0 : Int) values (0 : Int)))) (PreH8 : (y = (Znth 1 values (0 : Int)))) (PreH9 : (z = (Znth 2 values (0 : Int)))) (PreH10 : ((x + y) = (0 : Int))) (PreH11 : ((x + z) ≠ (0 : Int))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "x" ) )) # Int64 |-> (x))
  ** ((( &( "y" ) )) # Int64 |-> (y))
  ** ((( &( "z" ) )) # Int64 |-> (z))
  ** (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) 1 (y :: (@List.nil Int)))
  ** (int64Array.undef_seg b_pre 1 2)
  ** (int64Array.seg b_pre 2 3 (y :: (@List.nil Int)))
  ** (int64Array.undef_seg b_pre 3 n_pre)
|--
  “ ((x + z) ≠ (-9223372036854775808)) ”
) \/
(
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (start : Int) (x : Int) (y : Int) (z : Int) (PreH1 : (start = (0 : Int))) (PreH2 : (3 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Z.rem n_pre 2) ≠ (0 : Int))) (PreH6 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int))))) (PreH7 : (x = (Znth (0 : Int) values (0 : Int)))) (PreH8 : (y = (Znth 1 values (0 : Int)))) (PreH9 : (z = (Znth 2 values (0 : Int)))) (PreH10 : ((x + y) = (0 : Int))) (PreH11 : ((x + z) ≠ (0 : Int))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "x" ) )) # Int64 |-> (x))
  ** ((( &( "y" ) )) # Int64 |-> (y))
  ** ((( &( "z" ) )) # Int64 |-> (z))
  ** (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) 1 (y :: (@List.nil Int)))
  ** (int64Array.undef_seg b_pre 1 2)
  ** (int64Array.seg b_pre 2 3 (y :: (@List.nil Int)))
  ** (int64Array.undef_seg b_pre 3 n_pre)
|--
  “ ((x + z) ≠ (-9223372036854775808)) ”
)

noncomputable def solver_safety_wit_19_split_goal_1 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (start : Int) (x : Int) (y : Int) (z : Int) (PreH1 : (start = (0 : Int))) (PreH2 : (3 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Z.rem n_pre 2) ≠ (0 : Int))) (PreH6 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int))))) (PreH7 : (x = (Znth (0 : Int) values (0 : Int)))) (PreH8 : (y = (Znth 1 values (0 : Int)))) (PreH9 : (z = (Znth 2 values (0 : Int)))) (PreH10 : ((x + y) = (0 : Int))) (PreH11 : ((x + z) ≠ (0 : Int))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "x" ) )) # Int64 |-> (x))
  ** ((( &( "y" ) )) # Int64 |-> (y))
  ** ((( &( "z" ) )) # Int64 |-> (z))
  ** (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) 1 (y :: (@List.nil Int)))
  ** (int64Array.undef_seg b_pre 1 2)
  ** (int64Array.seg b_pre 2 3 (y :: (@List.nil Int)))
  ** (int64Array.undef_seg b_pre 3 n_pre)
|--
  “ ((x + z) ≠ (-9223372036854775808)) ”

noncomputable def solver_safety_wit_20 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (start : Int) (x : Int) (y : Int) (z : Int) (PreH1 : (start = (0 : Int))) (PreH2 : (3 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Z.rem n_pre 2) ≠ (0 : Int))) (PreH6 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int))))) (PreH7 : (x = (Znth (0 : Int) values (0 : Int)))) (PreH8 : (y = (Znth 1 values (0 : Int)))) (PreH9 : (z = (Znth 2 values (0 : Int)))) (PreH10 : ((x + y) = (0 : Int))) (PreH11 : ((x + z) ≠ (0 : Int))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "x" ) )) # Int64 |-> (x))
  ** ((( &( "y" ) )) # Int64 |-> (y))
  ** ((( &( "z" ) )) # Int64 |-> (z))
  ** (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) 1 (y :: (@List.nil Int)))
  ** (int64Array.undef_seg b_pre 1 2)
  ** (int64Array.seg b_pre 2 3 (y :: (@List.nil Int)))
  ** (int64Array.undef_seg b_pre 3 n_pre)
|--
  “ ((x + z) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (x + z)) ”
) \/
(
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (start : Int) (x : Int) (y : Int) (z : Int) (PreH1 : (start = (0 : Int))) (PreH2 : (3 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Z.rem n_pre 2) ≠ (0 : Int))) (PreH6 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int))))) (PreH7 : (x = (Znth (0 : Int) values (0 : Int)))) (PreH8 : (y = (Znth 1 values (0 : Int)))) (PreH9 : (z = (Znth 2 values (0 : Int)))) (PreH10 : ((x + y) = (0 : Int))) (PreH11 : ((x + z) ≠ (0 : Int))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "x" ) )) # Int64 |-> (x))
  ** ((( &( "y" ) )) # Int64 |-> (y))
  ** ((( &( "z" ) )) # Int64 |-> (z))
  ** (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) 1 (y :: (@List.nil Int)))
  ** (int64Array.undef_seg b_pre 1 2)
  ** (int64Array.seg b_pre 2 3 (y :: (@List.nil Int)))
  ** (int64Array.undef_seg b_pre 3 n_pre)
|--
  “ ((x + z) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (x + z)) ”
)

noncomputable def solver_safety_wit_20_split_goal_1 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (start : Int) (x : Int) (y : Int) (z : Int) (PreH1 : (start = (0 : Int))) (PreH2 : (3 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Z.rem n_pre 2) ≠ (0 : Int))) (PreH6 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int))))) (PreH7 : (x = (Znth (0 : Int) values (0 : Int)))) (PreH8 : (y = (Znth 1 values (0 : Int)))) (PreH9 : (z = (Znth 2 values (0 : Int)))) (PreH10 : ((x + y) = (0 : Int))) (PreH11 : ((x + z) ≠ (0 : Int))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "x" ) )) # Int64 |-> (x))
  ** ((( &( "y" ) )) # Int64 |-> (y))
  ** ((( &( "z" ) )) # Int64 |-> (z))
  ** (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) 1 (y :: (@List.nil Int)))
  ** (int64Array.undef_seg b_pre 1 2)
  ** (int64Array.seg b_pre 2 3 (y :: (@List.nil Int)))
  ** (int64Array.undef_seg b_pre 3 n_pre)
|--
  “ ((x + z) <= 9223372036854775807) ”

noncomputable def solver_safety_wit_20_split_goal_2 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (start : Int) (x : Int) (y : Int) (z : Int) (PreH1 : (start = (0 : Int))) (PreH2 : (3 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Z.rem n_pre 2) ≠ (0 : Int))) (PreH6 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int))))) (PreH7 : (x = (Znth (0 : Int) values (0 : Int)))) (PreH8 : (y = (Znth 1 values (0 : Int)))) (PreH9 : (z = (Znth 2 values (0 : Int)))) (PreH10 : ((x + y) = (0 : Int))) (PreH11 : ((x + z) ≠ (0 : Int))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "x" ) )) # Int64 |-> (x))
  ** ((( &( "y" ) )) # Int64 |-> (y))
  ** ((( &( "z" ) )) # Int64 |-> (z))
  ** (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) 1 (y :: (@List.nil Int)))
  ** (int64Array.undef_seg b_pre 1 2)
  ** (int64Array.seg b_pre 2 3 (y :: (@List.nil Int)))
  ** (int64Array.undef_seg b_pre 3 n_pre)
|--
  “ ((-9223372036854775808) <= (x + z)) ”

noncomputable def solver_safety_wit_21 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (((Znth (0 : Int) values (0 : Int)) + (Znth 2 values (0 : Int))) = (0 : Int))) (PreH2 : (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) = (0 : Int))) (PreH3 : (3 <= n_pre)) (PreH4 : ((0 : Int) <= INT_MAX)) (PreH5 : ((0 : Int) >= INT_MIN)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "z" ) )) # Int64 |-> ((Znth 2 values (0 : Int))))
  ** ((( &( "y" ) )) # Int64 |-> ((Znth 1 values (0 : Int))))
  ** ((( &( "x" ) )) # Int64 |-> ((Znth (0 : Int) values (0 : Int))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "start" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** (int64Array.undef_full b_pre n_pre)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_22 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (((Znth (0 : Int) values (0 : Int)) + (Znth 2 values (0 : Int))) = (0 : Int))) (PreH2 : (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) = (0 : Int))) (PreH3 : (3 <= n_pre)) (PreH4 : ((0 : Int) <= INT_MAX)) (PreH5 : ((0 : Int) >= INT_MIN)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (int64Array.mixed_full b_pre n_pre (replace_Znth (1) ((Some ((Znth (0 : Int) values (0 : Int))))) ((repeat_Z (None) (n_pre)))))
  ** (intArray.full a_pre n_pre values)
  ** ((( &( "z" ) )) # Int64 |-> ((Znth 2 values (0 : Int))))
  ** ((( &( "y" ) )) # Int64 |-> ((Znth 1 values (0 : Int))))
  ** ((( &( "x" ) )) # Int64 |-> ((Znth (0 : Int) values (0 : Int))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "start" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_23 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (((Znth (0 : Int) values (0 : Int)) + (Znth 2 values (0 : Int))) = (0 : Int))) (PreH2 : (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) = (0 : Int))) (PreH3 : (3 <= n_pre)) (PreH4 : ((0 : Int) <= INT_MAX)) (PreH5 : ((0 : Int) >= INT_MIN)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (int64Array.mixed_full b_pre n_pre (replace_Znth (2) ((Some ((Znth (0 : Int) values (0 : Int))))) ((replace_Znth (1) ((Some ((Znth (0 : Int) values (0 : Int))))) ((repeat_Z (None) (n_pre)))))))
  ** (intArray.full a_pre n_pre values)
  ** ((( &( "z" ) )) # Int64 |-> ((Znth 2 values (0 : Int))))
  ** ((( &( "y" ) )) # Int64 |-> ((Znth 1 values (0 : Int))))
  ** ((( &( "x" ) )) # Int64 |-> ((Znth (0 : Int) values (0 : Int))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "start" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_24 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (((Znth (0 : Int) values (0 : Int)) + (Znth 2 values (0 : Int))) = (0 : Int))) (PreH2 : (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) = (0 : Int))) (PreH3 : (3 <= n_pre)) (PreH4 : ((0 : Int) <= INT_MAX)) (PreH5 : ((0 : Int) >= INT_MIN)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (int64Array.mixed_full b_pre n_pre (replace_Znth (2) ((Some ((Znth (0 : Int) values (0 : Int))))) ((replace_Znth (1) ((Some ((Znth (0 : Int) values (0 : Int))))) ((repeat_Z (None) (n_pre)))))))
  ** (intArray.full a_pre n_pre values)
  ** ((( &( "z" ) )) # Int64 |-> ((Znth 2 values (0 : Int))))
  ** ((( &( "y" ) )) # Int64 |-> ((Znth 1 values (0 : Int))))
  ** ((( &( "x" ) )) # Int64 |-> ((Znth (0 : Int) values (0 : Int))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "start" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
|--
  “ (((Znth 1 values (0 : Int)) + (Znth 2 values (0 : Int))) ≠ (-9223372036854775808)) ”

noncomputable def solver_safety_wit_25 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (((Znth (0 : Int) values (0 : Int)) + (Znth 2 values (0 : Int))) = (0 : Int))) (PreH2 : (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) = (0 : Int))) (PreH3 : (3 <= n_pre)) (PreH4 : ((0 : Int) <= INT_MAX)) (PreH5 : ((0 : Int) >= INT_MIN)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (int64Array.mixed_full b_pre n_pre (replace_Znth (2) ((Some ((Znth (0 : Int) values (0 : Int))))) ((replace_Znth (1) ((Some ((Znth (0 : Int) values (0 : Int))))) ((repeat_Z (None) (n_pre)))))))
  ** (intArray.full a_pre n_pre values)
  ** ((( &( "z" ) )) # Int64 |-> ((Znth 2 values (0 : Int))))
  ** ((( &( "y" ) )) # Int64 |-> ((Znth 1 values (0 : Int))))
  ** ((( &( "x" ) )) # Int64 |-> ((Znth (0 : Int) values (0 : Int))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "start" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
|--
  “ (((Znth 1 values (0 : Int)) + (Znth 2 values (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((Znth 1 values (0 : Int)) + (Znth 2 values (0 : Int)))) ”

noncomputable def solver_safety_wit_26 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) ≠ (0 : Int))) (PreH2 : (3 <= n_pre)) (PreH3 : ((0 : Int) <= INT_MAX)) (PreH4 : ((0 : Int) >= INT_MIN)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (int64Array.undef_seg b_pre ((1 + 1) + 1) n_pre)
  ** (((b_pre + (2 * sizeof(INT64)))) # Int64 |-> ((-((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))))))
  ** (((b_pre + (1 * sizeof(INT64)))) # Int64 |-> ((Znth 2 values (0 : Int))))
  ** (((b_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> ((Znth 2 values (0 : Int))))
  ** (intArray.full a_pre n_pre values)
  ** ((( &( "z" ) )) # Int64 |-> ((Znth 2 values (0 : Int))))
  ** ((( &( "y" ) )) # Int64 |-> ((Znth 1 values (0 : Int))))
  ** ((( &( "x" ) )) # Int64 |-> ((Znth (0 : Int) values (0 : Int))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "start" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
|--
  “ (3 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 3) ”

noncomputable def solver_safety_wit_27 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (start : Int) (x : Int) (y : Int) (z : Int) (PreH1 : (start = (0 : Int))) (PreH2 : (3 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Z.rem n_pre 2) ≠ (0 : Int))) (PreH6 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int))))) (PreH7 : (x = (Znth (0 : Int) values (0 : Int)))) (PreH8 : (y = (Znth 1 values (0 : Int)))) (PreH9 : (z = (Znth 2 values (0 : Int)))) (PreH10 : ((x + y) = (0 : Int))) (PreH11 : ((x + z) ≠ (0 : Int))) ,
  (int64Array.seg b_pre (0 : Int) (1 + 1) ((y :: (@List.nil Int)) ++ ((-(x + z)) :: (@List.nil Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "x" ) )) # Int64 |-> (x))
  ** ((( &( "y" ) )) # Int64 |-> (y))
  ** ((( &( "z" ) )) # Int64 |-> (z))
  ** (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre 2 3 (y :: (@List.nil Int)))
  ** (int64Array.undef_seg b_pre 3 n_pre)
|--
  “ (3 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 3) ”

noncomputable def solver_safety_wit_28 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (((Znth (0 : Int) values (0 : Int)) + (Znth 2 values (0 : Int))) = (0 : Int))) (PreH2 : (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) = (0 : Int))) (PreH3 : (3 <= n_pre)) (PreH4 : ((0 : Int) <= INT_MAX)) (PreH5 : ((0 : Int) >= INT_MIN)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (int64Array.mixed_full b_pre n_pre (replace_Znth ((0 : Int)) ((Some ((-((Znth 1 values (0 : Int)) + (Znth 2 values (0 : Int))))))) ((replace_Znth (2) ((Some ((Znth (0 : Int) values (0 : Int))))) ((replace_Znth (1) ((Some ((Znth (0 : Int) values (0 : Int))))) ((repeat_Z (None) (n_pre)))))))))
  ** (intArray.full a_pre n_pre values)
  ** ((( &( "z" ) )) # Int64 |-> ((Znth 2 values (0 : Int))))
  ** ((( &( "y" ) )) # Int64 |-> ((Znth 1 values (0 : Int))))
  ** ((( &( "x" ) )) # Int64 |-> ((Znth (0 : Int) values (0 : Int))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "start" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
|--
  “ (3 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 3) ”

noncomputable def solver_safety_wit_29 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (written : (List Int)) (i : Int) (start : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int))))) (PreH5 : (start = 3)) (PreH6 : ((0 : Int) <= start)) (PreH7 : (start <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH10 : ((Z.rem (i - start) 2) = (0 : Int))) (PreH11 : (OutputPrefix (sublist ((0 : Int)) (i) (values)) written (Z.quot (10000 * start) 3))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) i written)
  ** (int64Array.undef_seg b_pre i n_pre)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_30 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (written : (List Int)) (i : Int) (start : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int))))) (PreH5 : (start = (0 : Int))) (PreH6 : ((0 : Int) <= start)) (PreH7 : (start <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH10 : ((Z.rem (i - start) 2) = (0 : Int))) (PreH11 : (OutputPrefix (sublist ((0 : Int)) (i) (values)) written (Z.quot (10000 * start) 3))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) i written)
  ** (int64Array.undef_seg b_pre i n_pre)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_31 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (written : (List Int)) (i : Int) (start : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int))))) (PreH5 : (start = (0 : Int))) (PreH6 : ((0 : Int) <= start)) (PreH7 : (start <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH10 : ((Z.rem (i - start) 2) = (0 : Int))) (PreH11 : (OutputPrefix (sublist ((0 : Int)) (i) (values)) written (Z.quot (10000 * start) 3))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) i written)
  ** (int64Array.undef_seg b_pre i n_pre)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_32 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (written : (List Int)) (i : Int) (start : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int))))) (PreH5 : (start = 3)) (PreH6 : ((0 : Int) <= start)) (PreH7 : (start <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH10 : ((Z.rem (i - start) 2) = (0 : Int))) (PreH11 : (OutputPrefix (sublist ((0 : Int)) (i) (values)) written (Z.quot (10000 * start) 3))) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) i written)
  ** (int64Array.undef_seg b_pre i n_pre)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_33 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (written : (List Int)) (start : Int) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int))))) (PreH5 : (start = (0 : Int))) (PreH6 : ((0 : Int) <= start)) (PreH7 : (start <= i)) (PreH8 : ((i + 1) < n_pre)) (PreH9 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH10 : ((Z.rem (i - start) 2) = (0 : Int))) (PreH11 : (OutputPrefix (sublist ((0 : Int)) (i) (values)) written (Z.quot (10000 * start) 3))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.seg b_pre (0 : Int) i written)
  ** (int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2)
  ** (int64Array.undef_seg b_pre (i + 2) n_pre)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_34 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (written : (List Int)) (start : Int) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int))))) (PreH5 : (start = (0 : Int))) (PreH6 : ((0 : Int) <= start)) (PreH7 : (start <= i)) (PreH8 : ((i + 1) < n_pre)) (PreH9 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH10 : ((Z.rem (i - start) 2) = (0 : Int))) (PreH11 : (OutputPrefix (sublist ((0 : Int)) (i) (values)) written (Z.quot (10000 * start) 3))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.seg b_pre (0 : Int) i written)
  ** (int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2)
  ** (int64Array.undef_seg b_pre (i + 2) n_pre)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_35 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (written : (List Int)) (start : Int) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int))))) (PreH5 : (start = 3)) (PreH6 : ((0 : Int) <= start)) (PreH7 : (start <= i)) (PreH8 : ((i + 1) < n_pre)) (PreH9 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH10 : ((Z.rem (i - start) 2) = (0 : Int))) (PreH11 : (OutputPrefix (sublist ((0 : Int)) (i) (values)) written (Z.quot (10000 * start) 3))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.seg b_pre (0 : Int) i written)
  ** (int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2)
  ** (int64Array.undef_seg b_pre (i + 2) n_pre)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_36 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (written : (List Int)) (start : Int) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int))))) (PreH5 : (start = 3)) (PreH6 : ((0 : Int) <= start)) (PreH7 : (start <= i)) (PreH8 : ((i + 1) < n_pre)) (PreH9 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH10 : ((Z.rem (i - start) 2) = (0 : Int))) (PreH11 : (OutputPrefix (sublist ((0 : Int)) (i) (values)) written (Z.quot (10000 * start) 3))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.seg b_pre (0 : Int) i written)
  ** (int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2)
  ** (int64Array.undef_seg b_pre (i + 2) n_pre)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_37 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (written : (List Int)) (start : Int) (i : Int) (pair_out : (List Int)) (PreH1 : (OutputPrefix ((Znth i values (0 : Int)) :: ((Znth (i + 1) values (0 : Int)) :: (@List.nil Int))) pair_out (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int))))) (PreH6 : (start = (0 : Int))) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start <= i)) (PreH9 : ((i + 1) < n_pre)) (PreH10 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH11 : ((Z.rem (i - start) 2) = (0 : Int))) (PreH12 : (OutputPrefix (sublist ((0 : Int)) (i) (values)) written (Z.quot (10000 * start) 3))) ,
  (int64Array.full (b_pre + (i * sizeof(INT64))) 2 pair_out)
  ** (intArray.full a_pre n_pre values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.seg b_pre (0 : Int) i written)
  ** (int64Array.undef_seg b_pre (i + 2) n_pre)
|--
  “ ((i + 2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 2)) ”

noncomputable def solver_safety_wit_38 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (written : (List Int)) (start : Int) (i : Int) (pair_out : (List Int)) (PreH1 : (OutputPrefix ((Znth i values (0 : Int)) :: ((Znth (i + 1) values (0 : Int)) :: (@List.nil Int))) pair_out (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int))))) (PreH6 : (start = (0 : Int))) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start <= i)) (PreH9 : ((i + 1) < n_pre)) (PreH10 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH11 : ((Z.rem (i - start) 2) = (0 : Int))) (PreH12 : (OutputPrefix (sublist ((0 : Int)) (i) (values)) written (Z.quot (10000 * start) 3))) ,
  (int64Array.full (b_pre + (i * sizeof(INT64))) 2 pair_out)
  ** (intArray.full a_pre n_pre values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.seg b_pre (0 : Int) i written)
  ** (int64Array.undef_seg b_pre (i + 2) n_pre)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_39 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (written : (List Int)) (start : Int) (i : Int) (pair_out : (List Int)) (PreH1 : (OutputPrefix ((Znth i values (0 : Int)) :: ((Znth (i + 1) values (0 : Int)) :: (@List.nil Int))) pair_out (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int))))) (PreH6 : (start = 3)) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start <= i)) (PreH9 : ((i + 1) < n_pre)) (PreH10 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH11 : ((Z.rem (i - start) 2) = (0 : Int))) (PreH12 : (OutputPrefix (sublist ((0 : Int)) (i) (values)) written (Z.quot (10000 * start) 3))) ,
  (int64Array.full (b_pre + (i * sizeof(INT64))) 2 pair_out)
  ** (intArray.full a_pre n_pre values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.seg b_pre (0 : Int) i written)
  ** (int64Array.undef_seg b_pre (i + 2) n_pre)
|--
  “ ((i + 2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 2)) ”

noncomputable def solver_safety_wit_40 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (written : (List Int)) (start : Int) (i : Int) (pair_out : (List Int)) (PreH1 : (OutputPrefix ((Znth i values (0 : Int)) :: ((Znth (i + 1) values (0 : Int)) :: (@List.nil Int))) pair_out (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int))))) (PreH6 : (start = 3)) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start <= i)) (PreH9 : ((i + 1) < n_pre)) (PreH10 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH11 : ((Z.rem (i - start) 2) = (0 : Int))) (PreH12 : (OutputPrefix (sublist ((0 : Int)) (i) (values)) written (Z.quot (10000 * start) 3))) ,
  (int64Array.full (b_pre + (i * sizeof(INT64))) 2 pair_out)
  ** (intArray.full a_pre n_pre values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.seg b_pre (0 : Int) i written)
  ** (int64Array.undef_seg b_pre (i + 2) n_pre)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  ((( &( "start" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** (intArray.full a_pre n_pre values)
  ** (int64Array.undef_full b_pre n_pre)
|--
  “ (3 <= n_pre) ” &&
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((0 : Int) >= INT_MIN) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int)))) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ ((Z.rem n_pre 2) ≠ (0 : Int)) ”
  &&  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "start" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** (intArray.full a_pre n_pre values)
  ** (int64Array.undef_full b_pre n_pre)
) \/
(
forall (values : (List Int)) (n_pre : Int) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : ((0 : Int) <= INT_MAX)) (PreH3 : (n_pre >= INT_MIN)) (PreH4 : ((0 : Int) >= INT_MIN)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (3 <= n_pre) ”
  &&  emp
)

noncomputable def solver_entail_wit_1_split_goal_1 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : ((0 : Int) <= INT_MAX)) (PreH3 : (n_pre >= INT_MIN)) (PreH4 : ((0 : Int) >= INT_MIN)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (3 <= n_pre)

noncomputable def solver_entail_wit_2 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (((Znth (0 : Int) values (0 : Int)) + (Znth 2 values (0 : Int))) ≠ (0 : Int))) (PreH2 : (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) = (0 : Int))) (PreH3 : (3 <= n_pre)) (PreH4 : ((0 : Int) <= INT_MAX)) (PreH5 : ((0 : Int) >= INT_MIN)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (int64Array.mixed_seg b_pre 1 n_pre (replace_Znth ((2 - 1)) ((Some ((Znth 1 values (0 : Int))))) ((repeat_Z (None) ((n_pre - 1))))))
  ** (((b_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> ((Znth 1 values (0 : Int))))
  ** (intArray.full a_pre n_pre values)
|--
  “ ((0 : Int) = (0 : Int)) ” &&
  “ (3 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ ((Z.rem n_pre 2) ≠ (0 : Int)) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int)))) ” &&
  “ ((Znth (0 : Int) values (0 : Int)) = (Znth (0 : Int) values (0 : Int))) ” &&
  “ ((Znth 1 values (0 : Int)) = (Znth 1 values (0 : Int))) ” &&
  “ ((Znth 2 values (0 : Int)) = (Znth 2 values (0 : Int))) ” &&
  “ (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) = (0 : Int)) ” &&
  “ (((Znth (0 : Int) values (0 : Int)) + (Znth 2 values (0 : Int))) ≠ (0 : Int)) ”
  &&  (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) 1 ((Znth 1 values (0 : Int)) :: (@List.nil Int)))
  ** (int64Array.undef_seg b_pre 1 2)
  ** (int64Array.seg b_pre 2 3 ((Znth 1 values (0 : Int)) :: (@List.nil Int)))
  ** (int64Array.undef_seg b_pre 3 n_pre)
) \/
(
forall (values : (List Int)) (n_pre : Int) (b_pre : Int) (PreH1 : ((Znth 1 values (0 : Int)) <= 9223372036854775807)) (PreH2 : ((Znth 1 values (0 : Int)) >= (-9223372036854775808))) (PreH3 : (((Znth (0 : Int) values (0 : Int)) + (Znth 2 values (0 : Int))) ≠ (0 : Int))) (PreH4 : (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) = (0 : Int))) (PreH5 : (3 <= n_pre)) (PreH6 : ((0 : Int) <= INT_MAX)) (PreH7 : ((0 : Int) >= INT_MIN)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= 100000)) (PreH10 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (int64Array.mixed_seg b_pre 1 n_pre (replace_Znth ((2 - 1)) ((Some ((Znth 1 values (0 : Int))))) ((repeat_Z (None) ((n_pre - 1))))))
  ** (((b_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> ((Znth 1 values (0 : Int))))
|--
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int)))) ”
  &&  (int64Array.seg b_pre (0 : Int) 1 ((Znth 1 values (0 : Int)) :: (@List.nil Int)))
  ** (int64Array.undef_seg b_pre 1 2)
  ** (int64Array.seg b_pre 2 3 ((Znth 1 values (0 : Int)) :: (@List.nil Int)))
  ** (int64Array.undef_seg b_pre 3 n_pre)
)

noncomputable def solver_entail_wit_2_split_goal_1 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (b_pre : Int) (PreH1 : ((Znth 1 values (0 : Int)) <= 9223372036854775807)) (PreH2 : ((Znth 1 values (0 : Int)) >= (-9223372036854775808))) (PreH3 : (((Znth (0 : Int) values (0 : Int)) + (Znth 2 values (0 : Int))) ≠ (0 : Int))) (PreH4 : (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) = (0 : Int))) (PreH5 : (3 <= n_pre)) (PreH6 : ((0 : Int) <= INT_MAX)) (PreH7 : ((0 : Int) >= INT_MIN)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= 100000)) (PreH10 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (int64Array.mixed_seg b_pre 1 n_pre (replace_Znth ((2 - 1)) ((Some ((Znth 1 values (0 : Int))))) ((repeat_Z (None) ((n_pre - 1))))))
  ** (((b_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> ((Znth 1 values (0 : Int))))
|--
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int)))) ”

noncomputable def solver_entail_wit_2_split_goal_spatial : Prop :=
  forall (values : (List Int)) (n_pre : Int) (b_pre : Int) (PreH1 : ((Znth 1 values (0 : Int)) <= 9223372036854775807)) (PreH2 : ((Znth 1 values (0 : Int)) >= (-9223372036854775808))) (PreH3 : (((Znth (0 : Int) values (0 : Int)) + (Znth 2 values (0 : Int))) ≠ (0 : Int))) (PreH4 : (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) = (0 : Int))) (PreH5 : (3 <= n_pre)) (PreH6 : ((0 : Int) <= INT_MAX)) (PreH7 : ((0 : Int) >= INT_MIN)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= 100000)) (PreH10 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH11 : (n_pre = (Zlength (values)))) (PreH12 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (int64Array.mixed_seg b_pre 1 n_pre (replace_Znth ((2 - 1)) ((Some ((Znth 1 values (0 : Int))))) ((repeat_Z (None) ((n_pre - 1))))))
  ** (((b_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> ((Znth 1 values (0 : Int))))
|--
  (int64Array.seg b_pre (0 : Int) 1 ((Znth 1 values (0 : Int)) :: (@List.nil Int)))
  ** (int64Array.undef_seg b_pre 1 2)
  ** (int64Array.seg b_pre 2 3 ((Znth 1 values (0 : Int)) :: (@List.nil Int)))
  ** (int64Array.undef_seg b_pre 3 n_pre)

noncomputable def solver_entail_wit_3_1 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) ≠ (0 : Int))) (PreH2 : (3 <= n_pre)) (PreH3 : ((0 : Int) <= INT_MAX)) (PreH4 : ((0 : Int) >= INT_MIN)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (int64Array.undef_seg b_pre ((1 + 1) + 1) n_pre)
  ** (((b_pre + (2 * sizeof(INT64)))) # Int64 |-> ((-((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))))))
  ** (((b_pre + (1 * sizeof(INT64)))) # Int64 |-> ((Znth 2 values (0 : Int))))
  ** (((b_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> ((Znth 2 values (0 : Int))))
  ** (intArray.full a_pre n_pre values)
|--
  EX written : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int)))) ” &&
  “ (3 = 3) ” &&
  “ ((0 : Int) <= 3) ” &&
  “ (3 <= n_pre) ” &&
  “ ((Z.rem n_pre 2) = (Z.rem 3 2)) ” &&
  “ (OutputPrefix (sublist ((0 : Int)) (3) (values)) written (Z.quot (10000 * 3) 3)) ”
  &&  (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) 3 written)
  ** (int64Array.undef_seg b_pre 3 n_pre)
) \/
(
forall (values : (List Int)) (n_pre : Int) (b_pre : Int) (PreH1 : ((Znth 2 values (0 : Int)) <= 9223372036854775807)) (PreH2 : ((-((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int)))) <= 9223372036854775807)) (PreH3 : ((Znth 2 values (0 : Int)) >= (-9223372036854775808))) (PreH4 : ((-((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int)))) >= (-9223372036854775808))) (PreH5 : (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) ≠ (0 : Int))) (PreH6 : (3 <= n_pre)) (PreH7 : ((0 : Int) <= INT_MAX)) (PreH8 : ((0 : Int) >= INT_MIN)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 100000)) (PreH11 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH12 : (n_pre = (Zlength (values)))) (PreH13 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (((b_pre + (2 * sizeof(INT64)))) # Int64 |-> ((-((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))))))
  ** (((b_pre + (1 * sizeof(INT64)))) # Int64 |-> ((Znth 2 values (0 : Int))))
  ** (((b_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> ((Znth 2 values (0 : Int))))
|--
  EX written : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int)))) ” &&
  “ ((0 : Int) <= 3) ” &&
  “ (3 <= n_pre) ” &&
  “ ((Z.rem n_pre 2) = (Z.rem 3 2)) ” &&
  “ (OutputPrefix (sublist ((0 : Int)) (3) (values)) written (Z.quot (10000 * 3) 3)) ”
  &&  (int64Array.seg b_pre (0 : Int) 3 written)
)

noncomputable def solver_entail_wit_3_2 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (start : Int) (x : Int) (y : Int) (z : Int) (PreH1 : (start = (0 : Int))) (PreH2 : (3 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Z.rem n_pre 2) ≠ (0 : Int))) (PreH6 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values (0 : Int))) ∧ ((Znth j_2 values (0 : Int)) <= 10000)) ∧ ((Znth j_2 values (0 : Int)) ≠ (0 : Int))))) (PreH7 : (x = (Znth (0 : Int) values (0 : Int)))) (PreH8 : (y = (Znth 1 values (0 : Int)))) (PreH9 : (z = (Znth 2 values (0 : Int)))) (PreH10 : ((x + y) = (0 : Int))) (PreH11 : ((x + z) ≠ (0 : Int))) ,
  (int64Array.seg b_pre (0 : Int) (1 + 1) ((y :: (@List.nil Int)) ++ ((-(x + z)) :: (@List.nil Int))))
  ** (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre 2 3 (y :: (@List.nil Int)))
  ** (int64Array.undef_seg b_pre 3 n_pre)
|--
  EX written : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int)))) ” &&
  “ (3 = 3) ” &&
  “ ((0 : Int) <= 3) ” &&
  “ (3 <= n_pre) ” &&
  “ ((Z.rem n_pre 2) = (Z.rem 3 2)) ” &&
  “ (OutputPrefix (sublist ((0 : Int)) (3) (values)) written (Z.quot (10000 * 3) 3)) ”
  &&  (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) 3 written)
  ** (int64Array.undef_seg b_pre 3 n_pre)
) \/
(
forall (values : (List Int)) (n_pre : Int) (b_pre : Int) (start : Int) (x : Int) (y : Int) (z : Int) (PreH1 : (start = (0 : Int))) (PreH2 : (3 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Z.rem n_pre 2) ≠ (0 : Int))) (PreH6 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values (0 : Int))) ∧ ((Znth j_2 values (0 : Int)) <= 10000)) ∧ ((Znth j_2 values (0 : Int)) ≠ (0 : Int))))) (PreH7 : (x = (Znth (0 : Int) values (0 : Int)))) (PreH8 : (y = (Znth 1 values (0 : Int)))) (PreH9 : (z = (Znth 2 values (0 : Int)))) (PreH10 : ((x + y) = (0 : Int))) (PreH11 : ((x + z) ≠ (0 : Int))) ,
  (int64Array.seg b_pre (0 : Int) (1 + 1) ((y :: (@List.nil Int)) ++ ((-(x + z)) :: (@List.nil Int))))
  ** (int64Array.seg b_pre 2 3 (y :: (@List.nil Int)))
|--
  EX written : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int)))) ” &&
  “ ((0 : Int) <= 3) ” &&
  “ (3 <= n_pre) ” &&
  “ ((Z.rem n_pre 2) = (Z.rem 3 2)) ” &&
  “ (OutputPrefix (sublist ((0 : Int)) (3) (values)) written (Z.quot (10000 * 3) 3)) ”
  &&  (int64Array.seg b_pre (0 : Int) 3 written)
)

noncomputable def solver_entail_wit_3_3 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (((Znth (0 : Int) values (0 : Int)) + (Znth 2 values (0 : Int))) = (0 : Int))) (PreH2 : (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) = (0 : Int))) (PreH3 : (3 <= n_pre)) (PreH4 : ((0 : Int) <= INT_MAX)) (PreH5 : ((0 : Int) >= INT_MIN)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (int64Array.mixed_full b_pre n_pre (replace_Znth ((0 : Int)) ((Some ((-((Znth 1 values (0 : Int)) + (Znth 2 values (0 : Int))))))) ((replace_Znth (2) ((Some ((Znth (0 : Int) values (0 : Int))))) ((replace_Znth (1) ((Some ((Znth (0 : Int) values (0 : Int))))) ((repeat_Z (None) (n_pre)))))))))
  ** (intArray.full a_pre n_pre values)
|--
  EX written : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int)))) ” &&
  “ (3 = 3) ” &&
  “ ((0 : Int) <= 3) ” &&
  “ (3 <= n_pre) ” &&
  “ ((Z.rem n_pre 2) = (Z.rem 3 2)) ” &&
  “ (OutputPrefix (sublist ((0 : Int)) (3) (values)) written (Z.quot (10000 * 3) 3)) ”
  &&  (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) 3 written)
  ** (int64Array.undef_seg b_pre 3 n_pre)
) \/
(
forall (values : (List Int)) (n_pre : Int) (b_pre : Int) (PreH1 : (((Znth (0 : Int) values (0 : Int)) + (Znth 2 values (0 : Int))) = (0 : Int))) (PreH2 : (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) = (0 : Int))) (PreH3 : (3 <= n_pre)) (PreH4 : ((0 : Int) <= INT_MAX)) (PreH5 : ((0 : Int) >= INT_MIN)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (int64Array.mixed_full b_pre n_pre (replace_Znth ((0 : Int)) ((Some ((-((Znth 1 values (0 : Int)) + (Znth 2 values (0 : Int))))))) ((replace_Znth (2) ((Some ((Znth (0 : Int) values (0 : Int))))) ((replace_Znth (1) ((Some ((Znth (0 : Int) values (0 : Int))))) ((repeat_Z (None) (n_pre)))))))))
|--
  EX written : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int)))) ” &&
  “ ((0 : Int) <= 3) ” &&
  “ (3 <= n_pre) ” &&
  “ ((Z.rem n_pre 2) = (Z.rem 3 2)) ” &&
  “ (OutputPrefix (sublist ((0 : Int)) (3) (values)) written (Z.quot (10000 * 3) 3)) ”
  &&  (int64Array.seg b_pre (0 : Int) 3 written)
  ** (int64Array.undef_seg b_pre 3 n_pre)
)

noncomputable def solver_entail_wit_3_4 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Z.rem n_pre 2) = (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** (int64Array.undef_full b_pre n_pre)
|--
  EX written : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int)))) ” &&
  “ ((0 : Int) = (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((Z.rem n_pre 2) = (Z.rem (0 : Int) 2)) ” &&
  “ (OutputPrefix (sublist ((0 : Int)) ((0 : Int)) (values)) written (Z.quot (10000 * (0 : Int)) 3)) ”
  &&  (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) (0 : Int) written)
  ** (int64Array.undef_seg b_pre (0 : Int) n_pre)
) \/
(
forall (values : (List Int)) (n_pre : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Z.rem n_pre 2) = (0 : Int))) ,
  TT && emp 
|--
  “ (OutputPrefix (sublist ((0 : Int)) ((0 : Int)) (values)) (@List.nil Int) (Z.quot (10000 * (0 : Int)) 3)) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int)))) ”
  &&  emp
)

noncomputable def solver_entail_wit_3_4_split_goal_1 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Z.rem n_pre 2) = (0 : Int))) ,
  (OutputPrefix (sublist ((0 : Int)) ((0 : Int)) (values)) (@List.nil Int) (Z.quot (10000 * (0 : Int)) 3))

noncomputable def solver_entail_wit_3_4_split_goal_2 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Z.rem n_pre 2) = (0 : Int))) ,
  forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int))))

noncomputable def solver_entail_wit_4_1 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (written_2 : (List Int)) (start : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values (0 : Int))) ∧ ((Znth j_2 values (0 : Int)) <= 10000)) ∧ ((Znth j_2 values (0 : Int)) ≠ (0 : Int))))) (PreH5 : (start = (0 : Int))) (PreH6 : ((0 : Int) <= start)) (PreH7 : (start <= n_pre)) (PreH8 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH9 : (OutputPrefix (sublist ((0 : Int)) (start) (values)) written_2 (Z.quot (10000 * start) 3))) ,
  (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) start written_2)
  ** (int64Array.undef_seg b_pre start n_pre)
|--
  EX written : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int)))) ” &&
  “ (start = (0 : Int)) ” &&
  “ ((0 : Int) <= start) ” &&
  “ (start <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((Z.rem n_pre 2) = (Z.rem start 2)) ” &&
  “ ((Z.rem (start - start) 2) = (0 : Int)) ” &&
  “ (OutputPrefix (sublist ((0 : Int)) (start) (values)) written (Z.quot (10000 * start) 3)) ”
  &&  (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) start written)
  ** (int64Array.undef_seg b_pre start n_pre)
) \/
(
forall (values : (List Int)) (n_pre : Int) (written_2 : (List Int)) (start : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values (0 : Int))) ∧ ((Znth j_2 values (0 : Int)) <= 10000)) ∧ ((Znth j_2 values (0 : Int)) ≠ (0 : Int))))) (PreH5 : (start = (0 : Int))) (PreH6 : ((0 : Int) <= start)) (PreH7 : (start <= n_pre)) (PreH8 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH9 : (OutputPrefix (sublist ((0 : Int)) (start) (values)) written_2 (Z.quot (10000 * start) 3))) ,
  TT && emp 
|--
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int)))) ”
  &&  emp
)

noncomputable def solver_entail_wit_4_1_split_goal_1 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (written_2 : (List Int)) (start : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values (0 : Int))) ∧ ((Znth j_2 values (0 : Int)) <= 10000)) ∧ ((Znth j_2 values (0 : Int)) ≠ (0 : Int))))) (PreH5 : (start = (0 : Int))) (PreH6 : ((0 : Int) <= start)) (PreH7 : (start <= n_pre)) (PreH8 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH9 : (OutputPrefix (sublist ((0 : Int)) (start) (values)) written_2 (Z.quot (10000 * start) 3))) ,
  forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int))))

noncomputable def solver_entail_wit_4_2 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (written_2 : (List Int)) (start : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values (0 : Int))) ∧ ((Znth j_2 values (0 : Int)) <= 10000)) ∧ ((Znth j_2 values (0 : Int)) ≠ (0 : Int))))) (PreH5 : (start = 3)) (PreH6 : ((0 : Int) <= start)) (PreH7 : (start <= n_pre)) (PreH8 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH9 : (OutputPrefix (sublist ((0 : Int)) (start) (values)) written_2 (Z.quot (10000 * start) 3))) ,
  (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) start written_2)
  ** (int64Array.undef_seg b_pre start n_pre)
|--
  EX written : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int)))) ” &&
  “ (start = 3) ” &&
  “ ((0 : Int) <= start) ” &&
  “ (start <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((Z.rem n_pre 2) = (Z.rem start 2)) ” &&
  “ ((Z.rem (start - start) 2) = (0 : Int)) ” &&
  “ (OutputPrefix (sublist ((0 : Int)) (start) (values)) written (Z.quot (10000 * start) 3)) ”
  &&  (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) start written)
  ** (int64Array.undef_seg b_pre start n_pre)
) \/
(
forall (values : (List Int)) (n_pre : Int) (written_2 : (List Int)) (start : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values (0 : Int))) ∧ ((Znth j_2 values (0 : Int)) <= 10000)) ∧ ((Znth j_2 values (0 : Int)) ≠ (0 : Int))))) (PreH5 : (start = 3)) (PreH6 : ((0 : Int) <= start)) (PreH7 : (start <= n_pre)) (PreH8 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH9 : (OutputPrefix (sublist ((0 : Int)) (start) (values)) written_2 (Z.quot (10000 * start) 3))) ,
  TT && emp 
|--
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int)))) ”
  &&  emp
)

noncomputable def solver_entail_wit_4_2_split_goal_1 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (written_2 : (List Int)) (start : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values (0 : Int))) ∧ ((Znth j_2 values (0 : Int)) <= 10000)) ∧ ((Znth j_2 values (0 : Int)) ≠ (0 : Int))))) (PreH5 : (start = 3)) (PreH6 : ((0 : Int) <= start)) (PreH7 : (start <= n_pre)) (PreH8 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH9 : (OutputPrefix (sublist ((0 : Int)) (start) (values)) written_2 (Z.quot (10000 * start) 3))) ,
  forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int))))

noncomputable def solver_entail_wit_5_1 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (written_2 : (List Int)) (i : Int) (start : Int) (PreH1 : ((i + 1) < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values (0 : Int))) ∧ ((Znth j_2 values (0 : Int)) <= 10000)) ∧ ((Znth j_2 values (0 : Int)) ≠ (0 : Int))))) (PreH6 : (start = (0 : Int))) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH11 : ((Z.rem (i - start) 2) = (0 : Int))) (PreH12 : (OutputPrefix (sublist ((0 : Int)) (i) (values)) written_2 (Z.quot (10000 * start) 3))) ,
  (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) i written_2)
  ** (int64Array.undef_seg b_pre i n_pre)
|--
  EX written : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int)))) ” &&
  “ (start = (0 : Int)) ” &&
  “ ((0 : Int) <= start) ” &&
  “ (start <= i) ” &&
  “ ((i + 1) < n_pre) ” &&
  “ ((Z.rem n_pre 2) = (Z.rem start 2)) ” &&
  “ ((Z.rem (i - start) 2) = (0 : Int)) ” &&
  “ (OutputPrefix (sublist ((0 : Int)) (i) (values)) written (Z.quot (10000 * start) 3)) ”
  &&  (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) i written)
  ** (int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2)
  ** (int64Array.undef_seg b_pre (i + 2) n_pre)
) \/
(
forall (values : (List Int)) (n_pre : Int) (b_pre : Int) (written_2 : (List Int)) (i : Int) (start : Int) (PreH1 : ((i + 1) < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values (0 : Int))) ∧ ((Znth j_2 values (0 : Int)) <= 10000)) ∧ ((Znth j_2 values (0 : Int)) ≠ (0 : Int))))) (PreH6 : (start = (0 : Int))) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH11 : ((Z.rem (i - start) 2) = (0 : Int))) (PreH12 : (OutputPrefix (sublist ((0 : Int)) (i) (values)) written_2 (Z.quot (10000 * start) 3))) ,
  (int64Array.undef_seg b_pre i n_pre)
|--
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int)))) ”
  &&  (int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2)
  ** (int64Array.undef_seg b_pre (i + 2) n_pre)
)

noncomputable def solver_entail_wit_5_1_split_goal_1 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (b_pre : Int) (written_2 : (List Int)) (i : Int) (start : Int) (PreH1 : ((i + 1) < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values (0 : Int))) ∧ ((Znth j_2 values (0 : Int)) <= 10000)) ∧ ((Znth j_2 values (0 : Int)) ≠ (0 : Int))))) (PreH6 : (start = (0 : Int))) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH11 : ((Z.rem (i - start) 2) = (0 : Int))) (PreH12 : (OutputPrefix (sublist ((0 : Int)) (i) (values)) written_2 (Z.quot (10000 * start) 3))) ,
  (int64Array.undef_seg b_pre i n_pre)
|--
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int)))) ”

noncomputable def solver_entail_wit_5_1_split_goal_spatial : Prop :=
  forall (values : (List Int)) (n_pre : Int) (b_pre : Int) (written_2 : (List Int)) (i : Int) (start : Int) (PreH1 : ((i + 1) < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values (0 : Int))) ∧ ((Znth j_2 values (0 : Int)) <= 10000)) ∧ ((Znth j_2 values (0 : Int)) ≠ (0 : Int))))) (PreH6 : (start = (0 : Int))) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH11 : ((Z.rem (i - start) 2) = (0 : Int))) (PreH12 : (OutputPrefix (sublist ((0 : Int)) (i) (values)) written_2 (Z.quot (10000 * start) 3))) ,
  (int64Array.undef_seg b_pre i n_pre)
|--
  (int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2)
  ** (int64Array.undef_seg b_pre (i + 2) n_pre)

noncomputable def solver_entail_wit_5_2 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (written_2 : (List Int)) (i : Int) (start : Int) (PreH1 : ((i + 1) < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values (0 : Int))) ∧ ((Znth j_2 values (0 : Int)) <= 10000)) ∧ ((Znth j_2 values (0 : Int)) ≠ (0 : Int))))) (PreH6 : (start = 3)) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH11 : ((Z.rem (i - start) 2) = (0 : Int))) (PreH12 : (OutputPrefix (sublist ((0 : Int)) (i) (values)) written_2 (Z.quot (10000 * start) 3))) ,
  (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) i written_2)
  ** (int64Array.undef_seg b_pre i n_pre)
|--
  EX written : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int)))) ” &&
  “ (start = 3) ” &&
  “ ((0 : Int) <= start) ” &&
  “ (start <= i) ” &&
  “ ((i + 1) < n_pre) ” &&
  “ ((Z.rem n_pre 2) = (Z.rem start 2)) ” &&
  “ ((Z.rem (i - start) 2) = (0 : Int)) ” &&
  “ (OutputPrefix (sublist ((0 : Int)) (i) (values)) written (Z.quot (10000 * start) 3)) ”
  &&  (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) i written)
  ** (int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2)
  ** (int64Array.undef_seg b_pre (i + 2) n_pre)
) \/
(
forall (values : (List Int)) (n_pre : Int) (b_pre : Int) (written_2 : (List Int)) (i : Int) (start : Int) (PreH1 : ((i + 1) < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values (0 : Int))) ∧ ((Znth j_2 values (0 : Int)) <= 10000)) ∧ ((Znth j_2 values (0 : Int)) ≠ (0 : Int))))) (PreH6 : (start = 3)) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH11 : ((Z.rem (i - start) 2) = (0 : Int))) (PreH12 : (OutputPrefix (sublist ((0 : Int)) (i) (values)) written_2 (Z.quot (10000 * start) 3))) ,
  (int64Array.undef_seg b_pre i n_pre)
|--
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int)))) ”
  &&  (int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2)
  ** (int64Array.undef_seg b_pre (i + 2) n_pre)
)

noncomputable def solver_entail_wit_5_2_split_goal_1 : Prop :=
  forall (values : (List Int)) (n_pre : Int) (b_pre : Int) (written_2 : (List Int)) (i : Int) (start : Int) (PreH1 : ((i + 1) < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values (0 : Int))) ∧ ((Znth j_2 values (0 : Int)) <= 10000)) ∧ ((Znth j_2 values (0 : Int)) ≠ (0 : Int))))) (PreH6 : (start = 3)) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH11 : ((Z.rem (i - start) 2) = (0 : Int))) (PreH12 : (OutputPrefix (sublist ((0 : Int)) (i) (values)) written_2 (Z.quot (10000 * start) 3))) ,
  (int64Array.undef_seg b_pre i n_pre)
|--
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int)))) ”

noncomputable def solver_entail_wit_5_2_split_goal_spatial : Prop :=
  forall (values : (List Int)) (n_pre : Int) (b_pre : Int) (written_2 : (List Int)) (i : Int) (start : Int) (PreH1 : ((i + 1) < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values (0 : Int))) ∧ ((Znth j_2 values (0 : Int)) <= 10000)) ∧ ((Znth j_2 values (0 : Int)) ≠ (0 : Int))))) (PreH6 : (start = 3)) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH11 : ((Z.rem (i - start) 2) = (0 : Int))) (PreH12 : (OutputPrefix (sublist ((0 : Int)) (i) (values)) written_2 (Z.quot (10000 * start) 3))) ,
  (int64Array.undef_seg b_pre i n_pre)
|--
  (int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2)
  ** (int64Array.undef_seg b_pre (i + 2) n_pre)

noncomputable def solver_entail_wit_6_1 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (written_2 : (List Int)) (start : Int) (i : Int) (pair_out : (List Int)) (PreH1 : (OutputPrefix ((Znth i values (0 : Int)) :: ((Znth (i + 1) values (0 : Int)) :: (@List.nil Int))) pair_out (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values (0 : Int))) ∧ ((Znth j_2 values (0 : Int)) <= 10000)) ∧ ((Znth j_2 values (0 : Int)) ≠ (0 : Int))))) (PreH6 : (start = (0 : Int))) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start <= i)) (PreH9 : ((i + 1) < n_pre)) (PreH10 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH11 : ((Z.rem (i - start) 2) = (0 : Int))) (PreH12 : (OutputPrefix (sublist ((0 : Int)) (i) (values)) written_2 (Z.quot (10000 * start) 3))) ,
  (int64Array.full (b_pre + (i * sizeof(INT64))) 2 pair_out)
  ** (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) i written_2)
  ** (int64Array.undef_seg b_pre (i + 2) n_pre)
|--
  EX written : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int)))) ” &&
  “ (start = (0 : Int)) ” &&
  “ ((0 : Int) <= start) ” &&
  “ (start <= (i + 2)) ” &&
  “ ((i + 2) <= n_pre) ” &&
  “ ((Z.rem n_pre 2) = (Z.rem start 2)) ” &&
  “ ((Z.rem ((i + 2) - start) 2) = (0 : Int)) ” &&
  “ (OutputPrefix (sublist ((0 : Int)) ((i + 2)) (values)) written (Z.quot (10000 * start) 3)) ”
  &&  (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) (i + 2) written)
  ** (int64Array.undef_seg b_pre (i + 2) n_pre)
) \/
(
forall (values : (List Int)) (n_pre : Int) (b_pre : Int) (written_2 : (List Int)) (start : Int) (i : Int) (pair_out : (List Int)) (PreH1 : (OutputPrefix ((Znth i values (0 : Int)) :: ((Znth (i + 1) values (0 : Int)) :: (@List.nil Int))) pair_out (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values (0 : Int))) ∧ ((Znth j_2 values (0 : Int)) <= 10000)) ∧ ((Znth j_2 values (0 : Int)) ≠ (0 : Int))))) (PreH6 : (start = (0 : Int))) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start <= i)) (PreH9 : ((i + 1) < n_pre)) (PreH10 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH11 : ((Z.rem (i - start) 2) = (0 : Int))) (PreH12 : (OutputPrefix (sublist ((0 : Int)) (i) (values)) written_2 (Z.quot (10000 * start) 3))) ,
  (int64Array.full (b_pre + (i * sizeof(INT64))) 2 pair_out)
  ** (int64Array.seg b_pre (0 : Int) i written_2)
|--
  EX written : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int)))) ” &&
  “ (start = (0 : Int)) ” &&
  “ ((0 : Int) <= start) ” &&
  “ (start <= (i + 2)) ” &&
  “ ((i + 2) <= n_pre) ” &&
  “ ((Z.rem n_pre 2) = (Z.rem start 2)) ” &&
  “ ((Z.rem ((i + 2) - start) 2) = (0 : Int)) ” &&
  “ (OutputPrefix (sublist ((0 : Int)) ((i + 2)) (values)) written (Z.quot (10000 * start) 3)) ”
  &&  (int64Array.seg b_pre (0 : Int) (i + 2) written)
)

noncomputable def solver_entail_wit_6_2 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (written_2 : (List Int)) (start : Int) (i : Int) (pair_out : (List Int)) (PreH1 : (OutputPrefix ((Znth i values (0 : Int)) :: ((Znth (i + 1) values (0 : Int)) :: (@List.nil Int))) pair_out (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values (0 : Int))) ∧ ((Znth j_2 values (0 : Int)) <= 10000)) ∧ ((Znth j_2 values (0 : Int)) ≠ (0 : Int))))) (PreH6 : (start = 3)) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start <= i)) (PreH9 : ((i + 1) < n_pre)) (PreH10 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH11 : ((Z.rem (i - start) 2) = (0 : Int))) (PreH12 : (OutputPrefix (sublist ((0 : Int)) (i) (values)) written_2 (Z.quot (10000 * start) 3))) ,
  (int64Array.full (b_pre + (i * sizeof(INT64))) 2 pair_out)
  ** (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) i written_2)
  ** (int64Array.undef_seg b_pre (i + 2) n_pre)
|--
  EX written : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int)))) ” &&
  “ (start = 3) ” &&
  “ ((0 : Int) <= start) ” &&
  “ (start <= (i + 2)) ” &&
  “ ((i + 2) <= n_pre) ” &&
  “ ((Z.rem n_pre 2) = (Z.rem start 2)) ” &&
  “ ((Z.rem ((i + 2) - start) 2) = (0 : Int)) ” &&
  “ (OutputPrefix (sublist ((0 : Int)) ((i + 2)) (values)) written (Z.quot (10000 * start) 3)) ”
  &&  (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) (i + 2) written)
  ** (int64Array.undef_seg b_pre (i + 2) n_pre)
) \/
(
forall (values : (List Int)) (n_pre : Int) (b_pre : Int) (written_2 : (List Int)) (start : Int) (i : Int) (pair_out : (List Int)) (PreH1 : (OutputPrefix ((Znth i values (0 : Int)) :: ((Znth (i + 1) values (0 : Int)) :: (@List.nil Int))) pair_out (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < n_pre)) -> ((((-10000) <= (Znth j_2 values (0 : Int))) ∧ ((Znth j_2 values (0 : Int)) <= 10000)) ∧ ((Znth j_2 values (0 : Int)) ≠ (0 : Int))))) (PreH6 : (start = 3)) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start <= i)) (PreH9 : ((i + 1) < n_pre)) (PreH10 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH11 : ((Z.rem (i - start) 2) = (0 : Int))) (PreH12 : (OutputPrefix (sublist ((0 : Int)) (i) (values)) written_2 (Z.quot (10000 * start) 3))) ,
  (int64Array.full (b_pre + (i * sizeof(INT64))) 2 pair_out)
  ** (int64Array.seg b_pre (0 : Int) i written_2)
|--
  EX written : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int)))) ” &&
  “ (start = 3) ” &&
  “ ((0 : Int) <= start) ” &&
  “ (start <= (i + 2)) ” &&
  “ ((i + 2) <= n_pre) ” &&
  “ ((Z.rem n_pre 2) = (Z.rem start 2)) ” &&
  “ ((Z.rem ((i + 2) - start) 2) = (0 : Int)) ” &&
  “ (OutputPrefix (sublist ((0 : Int)) ((i + 2)) (values)) written (Z.quot (10000 * start) 3)) ”
  &&  (int64Array.seg b_pre (0 : Int) (i + 2) written)
)

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (written : (List Int)) (i : Int) (start : Int) (PreH1 : ((i + 1) >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int))))) (PreH6 : (start = (0 : Int))) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH11 : ((Z.rem (i - start) 2) = (0 : Int))) (PreH12 : (OutputPrefix (sublist ((0 : Int)) (i) (values)) written (Z.quot (10000 * start) 3))) ,
  (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) i written)
  ** (int64Array.undef_seg b_pre i n_pre)
|--
  EX out : (List Int),
  “ (Spec values out) ”
  &&  (intArray.full a_pre n_pre values)
  ** (int64Array.full b_pre n_pre out)
) \/
(
forall (values : (List Int)) (n_pre : Int) (b_pre : Int) (written : (List Int)) (i : Int) (start : Int) (PreH1 : ((i + 1) >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int))))) (PreH6 : (start = (0 : Int))) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH11 : ((Z.rem (i - start) 2) = (0 : Int))) (PreH12 : (OutputPrefix (sublist ((0 : Int)) (i) (values)) written (Z.quot (10000 * start) 3))) ,
  (int64Array.seg b_pre (0 : Int) i written)
  ** (int64Array.undef_seg b_pre i n_pre)
|--
  EX out : (List Int),
  “ (Spec values out) ”
  &&  (int64Array.full b_pre n_pre out)
)

noncomputable def solver_return_wit_2 : Prop :=
  (
forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (written : (List Int)) (i : Int) (start : Int) (PreH1 : ((i + 1) >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int))))) (PreH6 : (start = 3)) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH11 : ((Z.rem (i - start) 2) = (0 : Int))) (PreH12 : (OutputPrefix (sublist ((0 : Int)) (i) (values)) written (Z.quot (10000 * start) 3))) ,
  (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) i written)
  ** (int64Array.undef_seg b_pre i n_pre)
|--
  EX out : (List Int),
  “ (Spec values out) ”
  &&  (intArray.full a_pre n_pre values)
  ** (int64Array.full b_pre n_pre out)
) \/
(
forall (values : (List Int)) (n_pre : Int) (b_pre : Int) (written : (List Int)) (i : Int) (start : Int) (PreH1 : ((i + 1) >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int))))) (PreH6 : (start = 3)) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH11 : ((Z.rem (i - start) 2) = (0 : Int))) (PreH12 : (OutputPrefix (sublist ((0 : Int)) (i) (values)) written (Z.quot (10000 * start) 3))) ,
  (int64Array.seg b_pre (0 : Int) i written)
  ** (int64Array.undef_seg b_pre i n_pre)
|--
  EX out : (List Int),
  “ (Spec values out) ”
  &&  (int64Array.full b_pre n_pre out)
)

noncomputable def solver_partial_solve_wit_1 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (3 <= n_pre)) (PreH2 : ((0 : Int) <= INT_MAX)) (PreH3 : ((0 : Int) >= INT_MIN)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** (int64Array.undef_full b_pre n_pre)
|--
  “ (3 <= n_pre) ” &&
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((0 : Int) >= INT_MIN) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int)))) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ ((Z.rem n_pre 2) ≠ (0 : Int)) ”
  &&  (((a_pre + (2 * sizeof(INT)))) # Int |-> ((Znth 2 values (0 : Int))))
  ** (intArray.missing_i a_pre 2 (0 : Int) n_pre values)
  ** (int64Array.undef_full b_pre n_pre)

noncomputable def solver_partial_solve_wit_2 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (3 <= n_pre)) (PreH2 : ((0 : Int) <= INT_MAX)) (PreH3 : ((0 : Int) >= INT_MIN)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** (int64Array.undef_full b_pre n_pre)
|--
  “ (3 <= n_pre) ” &&
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((0 : Int) >= INT_MIN) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int)))) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ ((Z.rem n_pre 2) ≠ (0 : Int)) ”
  &&  (((a_pre + (1 * sizeof(INT)))) # Int |-> ((Znth 1 values (0 : Int))))
  ** (intArray.missing_i a_pre 1 (0 : Int) n_pre values)
  ** (int64Array.undef_full b_pre n_pre)

noncomputable def solver_partial_solve_wit_3 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (3 <= n_pre)) (PreH2 : ((0 : Int) <= INT_MAX)) (PreH3 : ((0 : Int) >= INT_MIN)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** (int64Array.undef_full b_pre n_pre)
|--
  “ (3 <= n_pre) ” &&
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((0 : Int) >= INT_MIN) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int)))) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ ((Z.rem n_pre 2) ≠ (0 : Int)) ”
  &&  (((a_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((Znth (0 : Int) values (0 : Int))))
  ** (intArray.missing_i a_pre (0 : Int) (0 : Int) n_pre values)
  ** (int64Array.undef_full b_pre n_pre)

noncomputable def solver_partial_solve_wit_4 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) ≠ (0 : Int))) (PreH2 : (3 <= n_pre)) (PreH3 : ((0 : Int) <= INT_MAX)) (PreH4 : ((0 : Int) >= INT_MIN)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** (int64Array.undef_full b_pre n_pre)
|--
  “ (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) ≠ (0 : Int)) ” &&
  “ (3 <= n_pre) ” &&
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((0 : Int) >= INT_MIN) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int)))) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ ((Z.rem n_pre 2) ≠ (0 : Int)) ”
  &&  (((b_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |->_)
  ** (int64Array.undef_seg b_pre 1 n_pre)
  ** (intArray.full a_pre n_pre values)

noncomputable def solver_partial_solve_wit_5 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) ≠ (0 : Int))) (PreH2 : (3 <= n_pre)) (PreH3 : ((0 : Int) <= INT_MAX)) (PreH4 : ((0 : Int) >= INT_MIN)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (((b_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> ((Znth 2 values (0 : Int))))
  ** (int64Array.undef_seg b_pre 1 n_pre)
  ** (intArray.full a_pre n_pre values)
|--
  “ (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) ≠ (0 : Int)) ” &&
  “ (3 <= n_pre) ” &&
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((0 : Int) >= INT_MIN) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int)))) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ ((Z.rem n_pre 2) ≠ (0 : Int)) ”
  &&  (((b_pre + (1 * sizeof(INT64)))) # Int64 |->_)
  ** (int64Array.undef_seg b_pre (1 + 1) n_pre)
  ** (((b_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> ((Znth 2 values (0 : Int))))
  ** (intArray.full a_pre n_pre values)

noncomputable def solver_partial_solve_wit_6 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) ≠ (0 : Int))) (PreH2 : (3 <= n_pre)) (PreH3 : ((0 : Int) <= INT_MAX)) (PreH4 : ((0 : Int) >= INT_MIN)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (((b_pre + (1 * sizeof(INT64)))) # Int64 |-> ((Znth 2 values (0 : Int))))
  ** (int64Array.undef_seg b_pre (1 + 1) n_pre)
  ** (((b_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> ((Znth 2 values (0 : Int))))
  ** (intArray.full a_pre n_pre values)
|--
  “ (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) ≠ (0 : Int)) ” &&
  “ (3 <= n_pre) ” &&
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((0 : Int) >= INT_MIN) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int)))) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ ((Z.rem n_pre 2) ≠ (0 : Int)) ”
  &&  (((b_pre + (2 * sizeof(INT64)))) # Int64 |->_)
  ** (int64Array.undef_missing_i b_pre 2 (1 + 1) n_pre)
  ** (((b_pre + (1 * sizeof(INT64)))) # Int64 |-> ((Znth 2 values (0 : Int))))
  ** (((b_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> ((Znth 2 values (0 : Int))))
  ** (intArray.full a_pre n_pre values)

noncomputable def solver_partial_solve_wit_7 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (((Znth (0 : Int) values (0 : Int)) + (Znth 2 values (0 : Int))) ≠ (0 : Int))) (PreH2 : (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) = (0 : Int))) (PreH3 : (3 <= n_pre)) (PreH4 : ((0 : Int) <= INT_MAX)) (PreH5 : ((0 : Int) >= INT_MIN)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** (int64Array.undef_full b_pre n_pre)
|--
  “ (((Znth (0 : Int) values (0 : Int)) + (Znth 2 values (0 : Int))) ≠ (0 : Int)) ” &&
  “ (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) = (0 : Int)) ” &&
  “ (3 <= n_pre) ” &&
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((0 : Int) >= INT_MIN) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int)))) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ ((Z.rem n_pre 2) ≠ (0 : Int)) ”
  &&  (((b_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |->_)
  ** (int64Array.undef_seg b_pre 1 n_pre)
  ** (intArray.full a_pre n_pre values)

noncomputable def solver_partial_solve_wit_8 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (((Znth (0 : Int) values (0 : Int)) + (Znth 2 values (0 : Int))) ≠ (0 : Int))) (PreH2 : (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) = (0 : Int))) (PreH3 : (3 <= n_pre)) (PreH4 : ((0 : Int) <= INT_MAX)) (PreH5 : ((0 : Int) >= INT_MIN)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (((b_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> ((Znth 1 values (0 : Int))))
  ** (int64Array.undef_seg b_pre 1 n_pre)
  ** (intArray.full a_pre n_pre values)
|--
  “ (((Znth (0 : Int) values (0 : Int)) + (Znth 2 values (0 : Int))) ≠ (0 : Int)) ” &&
  “ (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) = (0 : Int)) ” &&
  “ (3 <= n_pre) ” &&
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((0 : Int) >= INT_MIN) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int)))) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ ((Z.rem n_pre 2) ≠ (0 : Int)) ”
  &&  (((b_pre + (2 * sizeof(INT64)))) # Int64 |->_)
  ** (int64Array.undef_missing_i b_pre 2 1 n_pre)
  ** (((b_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |-> ((Znth 1 values (0 : Int))))
  ** (intArray.full a_pre n_pre values)

noncomputable def solver_partial_solve_wit_9 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (start : Int) (x : Int) (y : Int) (z : Int) (PreH1 : (start = (0 : Int))) (PreH2 : (3 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Z.rem n_pre 2) ≠ (0 : Int))) (PreH6 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int))))) (PreH7 : (x = (Znth (0 : Int) values (0 : Int)))) (PreH8 : (y = (Znth 1 values (0 : Int)))) (PreH9 : (z = (Znth 2 values (0 : Int)))) (PreH10 : ((x + y) = (0 : Int))) (PreH11 : ((x + z) ≠ (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) 1 (y :: (@List.nil Int)))
  ** (int64Array.undef_seg b_pre 1 2)
  ** (int64Array.seg b_pre 2 3 (y :: (@List.nil Int)))
  ** (int64Array.undef_seg b_pre 3 n_pre)
|--
  “ (start = (0 : Int)) ” &&
  “ (3 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ ((Z.rem n_pre 2) ≠ (0 : Int)) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int)))) ” &&
  “ (x = (Znth (0 : Int) values (0 : Int))) ” &&
  “ (y = (Znth 1 values (0 : Int))) ” &&
  “ (z = (Znth 2 values (0 : Int))) ” &&
  “ ((x + y) = (0 : Int)) ” &&
  “ ((x + z) ≠ (0 : Int)) ”
  &&  (((b_pre + (1 * sizeof(INT64)))) # Int64 |->_)
  ** (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) 1 (y :: (@List.nil Int)))
  ** (int64Array.seg b_pre 2 3 (y :: (@List.nil Int)))
  ** (int64Array.undef_seg b_pre 3 n_pre)

noncomputable def solver_partial_solve_wit_10 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (((Znth (0 : Int) values (0 : Int)) + (Znth 2 values (0 : Int))) = (0 : Int))) (PreH2 : (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) = (0 : Int))) (PreH3 : (3 <= n_pre)) (PreH4 : ((0 : Int) <= INT_MAX)) (PreH5 : ((0 : Int) >= INT_MIN)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (intArray.full a_pre n_pre values)
  ** (int64Array.undef_full b_pre n_pre)
|--
  “ (((Znth (0 : Int) values (0 : Int)) + (Znth 2 values (0 : Int))) = (0 : Int)) ” &&
  “ (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) = (0 : Int)) ” &&
  “ (3 <= n_pre) ” &&
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((0 : Int) >= INT_MIN) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int)))) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ ((Z.rem n_pre 2) ≠ (0 : Int)) ”
  &&  (((b_pre + (1 * sizeof(INT64)))) # Int64 |->_)
  ** (int64Array.undef_missing_i b_pre 1 (0 : Int) n_pre)
  ** (intArray.full a_pre n_pre values)

noncomputable def solver_partial_solve_wit_11 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (((Znth (0 : Int) values (0 : Int)) + (Znth 2 values (0 : Int))) = (0 : Int))) (PreH2 : (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) = (0 : Int))) (PreH3 : (3 <= n_pre)) (PreH4 : ((0 : Int) <= INT_MAX)) (PreH5 : ((0 : Int) >= INT_MIN)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (int64Array.mixed_full b_pre n_pre (replace_Znth (1) ((Some ((Znth (0 : Int) values (0 : Int))))) ((repeat_Z (None) (n_pre)))))
  ** (intArray.full a_pre n_pre values)
|--
  “ (((Znth (0 : Int) values (0 : Int)) + (Znth 2 values (0 : Int))) = (0 : Int)) ” &&
  “ (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) = (0 : Int)) ” &&
  “ (3 <= n_pre) ” &&
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((0 : Int) >= INT_MIN) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int)))) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ ((Z.rem n_pre 2) ≠ (0 : Int)) ”
  &&  (((b_pre + (2 * sizeof(INT64)))) # Int64 |->_)
  ** (int64Array.mixed_missing_i b_pre 2 (0 : Int) n_pre (replace_Znth (1) ((Some ((Znth (0 : Int) values (0 : Int))))) ((repeat_Z (None) (n_pre)))))
  ** (intArray.full a_pre n_pre values)

noncomputable def solver_partial_solve_wit_12 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (PreH1 : (((Znth (0 : Int) values (0 : Int)) + (Znth 2 values (0 : Int))) = (0 : Int))) (PreH2 : (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) = (0 : Int))) (PreH3 : (3 <= n_pre)) (PreH4 : ((0 : Int) <= INT_MAX)) (PreH5 : ((0 : Int) >= INT_MIN)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int))))) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : ((Z.rem n_pre 2) ≠ (0 : Int))) ,
  (int64Array.mixed_full b_pre n_pre (replace_Znth (2) ((Some ((Znth (0 : Int) values (0 : Int))))) ((replace_Znth (1) ((Some ((Znth (0 : Int) values (0 : Int))))) ((repeat_Z (None) (n_pre)))))))
  ** (intArray.full a_pre n_pre values)
|--
  “ (((Znth (0 : Int) values (0 : Int)) + (Znth 2 values (0 : Int))) = (0 : Int)) ” &&
  “ (((Znth (0 : Int) values (0 : Int)) + (Znth 1 values (0 : Int))) = (0 : Int)) ” &&
  “ (3 <= n_pre) ” &&
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((0 : Int) >= INT_MIN) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((-10000) <= (Znth i values (0 : Int))) ∧ ((Znth i values (0 : Int)) <= 10000)) ∧ ((Znth i values (0 : Int)) ≠ (0 : Int)))) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ ((Z.rem n_pre 2) ≠ (0 : Int)) ”
  &&  (((b_pre + ((0 : Int) * sizeof(INT64)))) # Int64 |->_)
  ** (int64Array.mixed_missing_i b_pre (0 : Int) (0 : Int) n_pre (replace_Znth (2) ((Some ((Znth (0 : Int) values (0 : Int))))) ((replace_Znth (1) ((Some ((Znth (0 : Int) values (0 : Int))))) ((repeat_Z (None) (n_pre)))))))
  ** (intArray.full a_pre n_pre values)

noncomputable def solver_partial_solve_wit_13 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (written : (List Int)) (start : Int) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int))))) (PreH5 : (start = (0 : Int))) (PreH6 : ((0 : Int) <= start)) (PreH7 : (start <= i)) (PreH8 : ((i + 1) < n_pre)) (PreH9 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH10 : ((Z.rem (i - start) 2) = (0 : Int))) (PreH11 : (OutputPrefix (sublist ((0 : Int)) (i) (values)) written (Z.quot (10000 * start) 3))) ,
  (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) i written)
  ** (int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2)
  ** (int64Array.undef_seg b_pre (i + 2) n_pre)
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int)))) ” &&
  “ (start = (0 : Int)) ” &&
  “ ((0 : Int) <= start) ” &&
  “ (start <= i) ” &&
  “ ((i + 1) < n_pre) ” &&
  “ ((Z.rem n_pre 2) = (Z.rem start 2)) ” &&
  “ ((Z.rem (i - start) 2) = (0 : Int)) ” &&
  “ (OutputPrefix (sublist ((0 : Int)) (i) (values)) written (Z.quot (10000 * start) 3)) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i values (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre values)
  ** (int64Array.seg b_pre (0 : Int) i written)
  ** (int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2)
  ** (int64Array.undef_seg b_pre (i + 2) n_pre)

noncomputable def solver_partial_solve_wit_14 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (written : (List Int)) (start : Int) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int))))) (PreH5 : (start = (0 : Int))) (PreH6 : ((0 : Int) <= start)) (PreH7 : (start <= i)) (PreH8 : ((i + 1) < n_pre)) (PreH9 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH10 : ((Z.rem (i - start) 2) = (0 : Int))) (PreH11 : (OutputPrefix (sublist ((0 : Int)) (i) (values)) written (Z.quot (10000 * start) 3))) ,
  (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) i written)
  ** (int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2)
  ** (int64Array.undef_seg b_pre (i + 2) n_pre)
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int)))) ” &&
  “ (start = (0 : Int)) ” &&
  “ ((0 : Int) <= start) ” &&
  “ (start <= i) ” &&
  “ ((i + 1) < n_pre) ” &&
  “ ((Z.rem n_pre 2) = (Z.rem start 2)) ” &&
  “ ((Z.rem (i - start) 2) = (0 : Int)) ” &&
  “ (OutputPrefix (sublist ((0 : Int)) (i) (values)) written (Z.quot (10000 * start) 3)) ”
  &&  (((a_pre + ((i + 1) * sizeof(INT)))) # Int |-> ((Znth (i + 1) values (0 : Int))))
  ** (intArray.missing_i a_pre (i + 1) (0 : Int) n_pre values)
  ** (int64Array.seg b_pre (0 : Int) i written)
  ** (int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2)
  ** (int64Array.undef_seg b_pre (i + 2) n_pre)

noncomputable def solver_partial_solve_wit_15 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (written : (List Int)) (start : Int) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int))))) (PreH5 : (start = 3)) (PreH6 : ((0 : Int) <= start)) (PreH7 : (start <= i)) (PreH8 : ((i + 1) < n_pre)) (PreH9 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH10 : ((Z.rem (i - start) 2) = (0 : Int))) (PreH11 : (OutputPrefix (sublist ((0 : Int)) (i) (values)) written (Z.quot (10000 * start) 3))) ,
  (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) i written)
  ** (int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2)
  ** (int64Array.undef_seg b_pre (i + 2) n_pre)
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int)))) ” &&
  “ (start = 3) ” &&
  “ ((0 : Int) <= start) ” &&
  “ (start <= i) ” &&
  “ ((i + 1) < n_pre) ” &&
  “ ((Z.rem n_pre 2) = (Z.rem start 2)) ” &&
  “ ((Z.rem (i - start) 2) = (0 : Int)) ” &&
  “ (OutputPrefix (sublist ((0 : Int)) (i) (values)) written (Z.quot (10000 * start) 3)) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> ((Znth i values (0 : Int))))
  ** (intArray.missing_i a_pre i (0 : Int) n_pre values)
  ** (int64Array.seg b_pre (0 : Int) i written)
  ** (int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2)
  ** (int64Array.undef_seg b_pre (i + 2) n_pre)

noncomputable def solver_partial_solve_wit_16 : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (written : (List Int)) (start : Int) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int))))) (PreH5 : (start = 3)) (PreH6 : ((0 : Int) <= start)) (PreH7 : (start <= i)) (PreH8 : ((i + 1) < n_pre)) (PreH9 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH10 : ((Z.rem (i - start) 2) = (0 : Int))) (PreH11 : (OutputPrefix (sublist ((0 : Int)) (i) (values)) written (Z.quot (10000 * start) 3))) ,
  (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) i written)
  ** (int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2)
  ** (int64Array.undef_seg b_pre (i + 2) n_pre)
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int)))) ” &&
  “ (start = 3) ” &&
  “ ((0 : Int) <= start) ” &&
  “ (start <= i) ” &&
  “ ((i + 1) < n_pre) ” &&
  “ ((Z.rem n_pre 2) = (Z.rem start 2)) ” &&
  “ ((Z.rem (i - start) 2) = (0 : Int)) ” &&
  “ (OutputPrefix (sublist ((0 : Int)) (i) (values)) written (Z.quot (10000 * start) 3)) ”
  &&  (((a_pre + ((i + 1) * sizeof(INT)))) # Int |-> ((Znth (i + 1) values (0 : Int))))
  ** (intArray.missing_i a_pre (i + 1) (0 : Int) n_pre values)
  ** (int64Array.seg b_pre (0 : Int) i written)
  ** (int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2)
  ** (int64Array.undef_seg b_pre (i + 2) n_pre)

noncomputable def solver_partial_solve_wit_17_pure : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (written : (List Int)) (start : Int) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int))))) (PreH5 : (start = (0 : Int))) (PreH6 : ((0 : Int) <= start)) (PreH7 : (start <= i)) (PreH8 : ((i + 1) < n_pre)) (PreH9 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH10 : ((Z.rem (i - start) 2) = (0 : Int))) (PreH11 : (OutputPrefix (sublist ((0 : Int)) (i) (values)) written (Z.quot (10000 * start) 3))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.seg b_pre (0 : Int) i written)
  ** (int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2)
  ** (int64Array.undef_seg b_pre (i + 2) n_pre)
|--
  “ ((-10000) <= (Znth i values (0 : Int))) ” &&
  “ ((Znth i values (0 : Int)) <= 10000) ” &&
  “ ((Znth i values (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((-10000) <= (Znth (i + 1) values (0 : Int))) ” &&
  “ ((Znth (i + 1) values (0 : Int)) <= 10000) ” &&
  “ ((Znth (i + 1) values (0 : Int)) ≠ (0 : Int)) ”

noncomputable def solver_partial_solve_wit_17_aux : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (written : (List Int)) (start : Int) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int))))) (PreH5 : (start = (0 : Int))) (PreH6 : ((0 : Int) <= start)) (PreH7 : (start <= i)) (PreH8 : ((i + 1) < n_pre)) (PreH9 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH10 : ((Z.rem (i - start) 2) = (0 : Int))) (PreH11 : (OutputPrefix (sublist ((0 : Int)) (i) (values)) written (Z.quot (10000 * start) 3))) ,
  (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) i written)
  ** (int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2)
  ** (int64Array.undef_seg b_pre (i + 2) n_pre)
|--
  “ ((-10000) <= (Znth i values (0 : Int))) ” &&
  “ ((Znth i values (0 : Int)) <= 10000) ” &&
  “ ((Znth i values (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((-10000) <= (Znth (i + 1) values (0 : Int))) ” &&
  “ ((Znth (i + 1) values (0 : Int)) <= 10000) ” &&
  “ ((Znth (i + 1) values (0 : Int)) ≠ (0 : Int)) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int)))) ” &&
  “ (start = (0 : Int)) ” &&
  “ ((0 : Int) <= start) ” &&
  “ (start <= i) ” &&
  “ ((i + 1) < n_pre) ” &&
  “ ((Z.rem n_pre 2) = (Z.rem start 2)) ” &&
  “ ((Z.rem (i - start) 2) = (0 : Int)) ” &&
  “ (OutputPrefix (sublist ((0 : Int)) (i) (values)) written (Z.quot (10000 * start) 3)) ”
  &&  (int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2)
  ** (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) i written)
  ** (int64Array.undef_seg b_pre (i + 2) n_pre)

noncomputable def solver_partial_solve_wit_17 : Prop := solver_partial_solve_wit_17_pure -> solver_partial_solve_wit_17_aux

noncomputable def solver_partial_solve_wit_18_pure : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (written : (List Int)) (start : Int) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int))))) (PreH5 : (start = 3)) (PreH6 : ((0 : Int) <= start)) (PreH7 : (start <= i)) (PreH8 : ((i + 1) < n_pre)) (PreH9 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH10 : ((Z.rem (i - start) 2) = (0 : Int))) (PreH11 : (OutputPrefix (sublist ((0 : Int)) (i) (values)) written (Z.quot (10000 * start) 3))) ,
  (intArray.full a_pre n_pre values)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64Array.seg b_pre (0 : Int) i written)
  ** (int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2)
  ** (int64Array.undef_seg b_pre (i + 2) n_pre)
|--
  “ ((-10000) <= (Znth i values (0 : Int))) ” &&
  “ ((Znth i values (0 : Int)) <= 10000) ” &&
  “ ((Znth i values (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((-10000) <= (Znth (i + 1) values (0 : Int))) ” &&
  “ ((Znth (i + 1) values (0 : Int)) <= 10000) ” &&
  “ ((Znth (i + 1) values (0 : Int)) ≠ (0 : Int)) ”

noncomputable def solver_partial_solve_wit_18_aux : Prop :=
  forall (values : (List Int)) (a_pre : Int) (n_pre : Int) (b_pre : Int) (written : (List Int)) (start : Int) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int))))) (PreH5 : (start = 3)) (PreH6 : ((0 : Int) <= start)) (PreH7 : (start <= i)) (PreH8 : ((i + 1) < n_pre)) (PreH9 : ((Z.rem n_pre 2) = (Z.rem start 2))) (PreH10 : ((Z.rem (i - start) 2) = (0 : Int))) (PreH11 : (OutputPrefix (sublist ((0 : Int)) (i) (values)) written (Z.quot (10000 * start) 3))) ,
  (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) i written)
  ** (int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2)
  ** (int64Array.undef_seg b_pre (i + 2) n_pre)
|--
  “ ((-10000) <= (Znth i values (0 : Int))) ” &&
  “ ((Znth i values (0 : Int)) <= 10000) ” &&
  “ ((Znth i values (0 : Int)) ≠ (0 : Int)) ” &&
  “ ((-10000) <= (Znth (i + 1) values (0 : Int))) ” &&
  “ ((Znth (i + 1) values (0 : Int)) <= 10000) ” &&
  “ ((Znth (i + 1) values (0 : Int)) ≠ (0 : Int)) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (n_pre = (Zlength (values))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < n_pre)) -> ((((-10000) <= (Znth j values (0 : Int))) ∧ ((Znth j values (0 : Int)) <= 10000)) ∧ ((Znth j values (0 : Int)) ≠ (0 : Int)))) ” &&
  “ (start = 3) ” &&
  “ ((0 : Int) <= start) ” &&
  “ (start <= i) ” &&
  “ ((i + 1) < n_pre) ” &&
  “ ((Z.rem n_pre 2) = (Z.rem start 2)) ” &&
  “ ((Z.rem (i - start) 2) = (0 : Int)) ” &&
  “ (OutputPrefix (sublist ((0 : Int)) (i) (values)) written (Z.quot (10000 * start) 3)) ”
  &&  (int64Array.undef_full (b_pre + (i * sizeof(INT64))) 2)
  ** (intArray.full a_pre n_pre values)
  ** (int64Array.seg b_pre (0 : Int) i written)
  ** (int64Array.undef_seg b_pre (i + 2) n_pre)

noncomputable def solver_partial_solve_wit_18 : Prop := solver_partial_solve_wit_18_pure -> solver_partial_solve_wit_18_aux


structure VC_Correct : Type where
  proof_of_llabs_safety_wit_1 : llabs_safety_wit_1
  proof_of_llabs_safety_wit_2 : llabs_safety_wit_2
  proof_of_gcdll_safety_wit_1 : gcdll_safety_wit_1
  proof_of_gcdll_safety_wit_2 : gcdll_safety_wit_2
  proof_of_gcdll_safety_wit_3 : gcdll_safety_wit_3
  proof_of_gcdll_entail_wit_1 : gcdll_entail_wit_1
  proof_of_pair_fill_safety_wit_1 : pair_fill_safety_wit_1
  proof_of_pair_fill_safety_wit_3 : pair_fill_safety_wit_3
  proof_of_pair_fill_safety_wit_5 : pair_fill_safety_wit_5
  proof_of_pair_fill_partial_solve_wit_1_pure : pair_fill_partial_solve_wit_1_pure
  proof_of_pair_fill_partial_solve_wit_1 : pair_fill_partial_solve_wit_1
  proof_of_pair_fill_partial_solve_wit_2_pure : pair_fill_partial_solve_wit_2_pure
  proof_of_pair_fill_partial_solve_wit_2 : pair_fill_partial_solve_wit_2
  proof_of_pair_fill_partial_solve_wit_3 : pair_fill_partial_solve_wit_3
  proof_of_pair_fill_partial_solve_wit_4 : pair_fill_partial_solve_wit_4
  proof_of_pair_fill_partial_solve_wit_5 : pair_fill_partial_solve_wit_5
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
  proof_of_solver_partial_solve_wit_17_pure : solver_partial_solve_wit_17_pure
  proof_of_solver_partial_solve_wit_17 : solver_partial_solve_wit_17
  proof_of_solver_partial_solve_wit_18_pure : solver_partial_solve_wit_18_pure
  proof_of_solver_partial_solve_wit_18 : solver_partial_solve_wit_18
  proof_of_llabs_return_wit_1 : llabs_return_wit_1
  proof_of_llabs_return_wit_2 : llabs_return_wit_2
  proof_of_gcdll_entail_wit_2 : gcdll_entail_wit_2
  proof_of_gcdll_return_wit_1 : gcdll_return_wit_1
  proof_of_pair_fill_safety_wit_2 : pair_fill_safety_wit_2
  proof_of_pair_fill_safety_wit_4 : pair_fill_safety_wit_4
  proof_of_pair_fill_return_wit_1 : pair_fill_return_wit_1
  proof_of_pair_fill_partial_solve_wit_3_pure : pair_fill_partial_solve_wit_3_pure
  proof_of_solver_safety_wit_19 : solver_safety_wit_19
  proof_of_solver_safety_wit_20 : solver_safety_wit_20
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_2 : solver_entail_wit_2
  proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1
  proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2
  proof_of_solver_entail_wit_3_3 : solver_entail_wit_3_3
  proof_of_solver_entail_wit_3_4 : solver_entail_wit_3_4
  proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1
  proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2
  proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1
  proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2
  proof_of_solver_entail_wit_6_1 : solver_entail_wit_6_1
  proof_of_solver_entail_wit_6_2 : solver_entail_wit_6_2
  proof_of_solver_return_wit_1 : solver_return_wit_1
  proof_of_solver_return_wit_2 : solver_return_wit_2

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P047_1582D_vupsen_pupsen_and_0_goal
