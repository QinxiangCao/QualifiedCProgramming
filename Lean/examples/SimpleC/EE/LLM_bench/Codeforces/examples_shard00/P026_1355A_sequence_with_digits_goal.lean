import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P026_1355A_sequence_with_digits_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P026_1355A_sequence_with_digits_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P026_1355A_sequence_with_digits_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P026_1355A_sequence_with_digits_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def step_safety_wit_1 : Prop :=
  forall (x_pre : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1810000000000000000)) ,
  ((( &( "mx" ) )) # Int |->_)
  ** ((( &( "mn" ) )) # Int |-> (9))
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def step_safety_wit_2 : Prop :=
  forall (x_pre : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1810000000000000000)) ,
  ((( &( "mn" ) )) # Int |->_)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
|--
  “ (9 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 9) ”

noncomputable def step_safety_wit_3 : Prop :=
  forall (x_pre : Int) (mx : Int) (mn : Int) (x : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1810000000000000000)) (PreH3 : ((0 : Int) <= x)) (PreH4 : (x <= x_pre)) (PreH5 : ((0 : Int) <= mn)) (PreH6 : (mn <= 9)) (PreH7 : ((0 : Int) <= mx)) (PreH8 : (mx <= 9)) (PreH9 : (DigitScanState x_pre x mn mx)) (PreH10 : (x ≠ (0 : Int))) ,
  ((( &( "d" ) )) # Int |->_)
  ** ((( &( "x" ) )) # Int64 |-> (x))
  ** ((( &( "mn" ) )) # Int |-> (mn))
  ** ((( &( "mx" ) )) # Int |-> (mx))
|--
  “ ((x ≠ (-9223372036854775808)) ∨ (10 ≠ (-1))) ” &&
  “ (10 ≠ (0 : Int)) ”

noncomputable def step_safety_wit_4 : Prop :=
  forall (x_pre : Int) (mx : Int) (mn : Int) (x : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1810000000000000000)) (PreH3 : ((0 : Int) <= x)) (PreH4 : (x <= x_pre)) (PreH5 : ((0 : Int) <= mn)) (PreH6 : (mn <= 9)) (PreH7 : ((0 : Int) <= mx)) (PreH8 : (mx <= 9)) (PreH9 : (DigitScanState x_pre x mn mx)) (PreH10 : (x ≠ (0 : Int))) ,
  ((( &( "d" ) )) # Int |->_)
  ** ((( &( "x" ) )) # Int64 |-> (x))
  ** ((( &( "mn" ) )) # Int |-> (mn))
  ** ((( &( "mx" ) )) # Int |-> (mx))
|--
  “ (10 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 10) ”

noncomputable def step_safety_wit_5 : Prop :=
  forall (x_pre : Int) (mx : Int) (mn : Int) (x : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1810000000000000000)) (PreH3 : ((0 : Int) <= x)) (PreH4 : (x <= x_pre)) (PreH5 : ((0 : Int) <= mn)) (PreH6 : (mn <= 9)) (PreH7 : ((0 : Int) <= mx)) (PreH8 : (mx <= 9)) (PreH9 : (DigitScanState x_pre x mn mx)) (PreH10 : (x ≠ (0 : Int))) ,
  ((( &( "d" ) )) # Int |-> ((signed_last_nbits ((Z.rem x 10)) (32))))
  ** ((( &( "x" ) )) # Int64 |-> (x))
  ** ((( &( "mn" ) )) # Int |-> (mn))
  ** ((( &( "mx" ) )) # Int |-> (mx))
|--
  “ ((x ≠ (-9223372036854775808)) ∨ (10 ≠ (-1))) ” &&
  “ (10 ≠ (0 : Int)) ”

noncomputable def step_safety_wit_6 : Prop :=
  forall (x_pre : Int) (mx : Int) (mn : Int) (x : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1810000000000000000)) (PreH3 : ((0 : Int) <= x)) (PreH4 : (x <= x_pre)) (PreH5 : ((0 : Int) <= mn)) (PreH6 : (mn <= 9)) (PreH7 : ((0 : Int) <= mx)) (PreH8 : (mx <= 9)) (PreH9 : (DigitScanState x_pre x mn mx)) (PreH10 : (x ≠ (0 : Int))) ,
  ((( &( "d" ) )) # Int |-> ((signed_last_nbits ((Z.rem x 10)) (32))))
  ** ((( &( "x" ) )) # Int64 |-> (x))
  ** ((( &( "mn" ) )) # Int |-> (mn))
  ** ((( &( "mx" ) )) # Int |-> (mx))
|--
  “ (10 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 10) ”

noncomputable def step_safety_wit_7 : Prop :=
  forall (x_pre : Int) (mx : Int) (mn : Int) (x : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1810000000000000000)) (PreH3 : ((0 : Int) <= x)) (PreH4 : (x <= x_pre)) (PreH5 : ((0 : Int) <= mn)) (PreH6 : (mn <= 9)) (PreH7 : ((0 : Int) <= mx)) (PreH8 : (mx <= 9)) (PreH9 : (DigitScanState x_pre x mn mx)) (PreH10 : (x = (0 : Int))) ,
  ((( &( "x" ) )) # Int64 |-> (x))
  ** ((( &( "mn" ) )) # Int |-> (mn))
  ** ((( &( "mx" ) )) # Int |-> (mx))
|--
  “ ((mn * mx) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (mn * mx)) ”

noncomputable def step_entail_wit_1 : Prop :=
  (
forall (x_pre : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1810000000000000000)) ,
  TT && emp 
|--
  “ (1 <= x_pre) ” &&
  “ (x_pre <= 1810000000000000000) ” &&
  “ ((0 : Int) <= x_pre) ” &&
  “ (x_pre <= x_pre) ” &&
  “ ((0 : Int) <= 9) ” &&
  “ (9 <= 9) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 9) ” &&
  “ (DigitScanState x_pre x_pre 9 (0 : Int)) ”
  &&  emp
) \/
(
forall (x_pre : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1810000000000000000)) ,
  TT && emp 
|--
  “ (DigitScanState x_pre x_pre 9 (0 : Int)) ”
  &&  emp
)

noncomputable def step_entail_wit_1_split_goal_1 : Prop :=
  forall (x_pre : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1810000000000000000)) ,
  (DigitScanState x_pre x_pre 9 (0 : Int))

noncomputable def step_entail_wit_2_1 : Prop :=
  (
forall (x_pre : Int) (mx : Int) (mn : Int) (x : Int) (PreH1 : ((signed_last_nbits ((Z.rem x 10)) (32)) > mx)) (PreH2 : ((signed_last_nbits ((Z.rem x 10)) (32)) < mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : ((0 : Int) <= x)) (PreH6 : (x <= x_pre)) (PreH7 : ((0 : Int) <= mn)) (PreH8 : (mn <= 9)) (PreH9 : ((0 : Int) <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx)) (PreH12 : (x ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (1 <= x_pre) ” &&
  “ (x_pre <= 1810000000000000000) ” &&
  “ ((0 : Int) <= (Z.quot x 10)) ” &&
  “ ((Z.quot x 10) <= x_pre) ” &&
  “ ((0 : Int) <= (signed_last_nbits ((Z.rem x 10)) (32))) ” &&
  “ ((signed_last_nbits ((Z.rem x 10)) (32)) <= 9) ” &&
  “ ((0 : Int) <= (signed_last_nbits ((Z.rem x 10)) (32))) ” &&
  “ ((signed_last_nbits ((Z.rem x 10)) (32)) <= 9) ” &&
  “ (DigitScanState x_pre (Z.quot x 10) (signed_last_nbits ((Z.rem x 10)) (32)) (signed_last_nbits ((Z.rem x 10)) (32))) ”
  &&  emp
) \/
(
forall (x_pre : Int) (mx : Int) (mn : Int) (x : Int) (PreH1 : ((signed_last_nbits ((Z.rem x 10)) (32)) > mx)) (PreH2 : ((signed_last_nbits ((Z.rem x 10)) (32)) < mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : ((0 : Int) <= x)) (PreH6 : (x <= x_pre)) (PreH7 : ((0 : Int) <= mn)) (PreH8 : (mn <= 9)) (PreH9 : ((0 : Int) <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx)) (PreH12 : (x ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (DigitScanState x_pre (Z.quot x 10) (signed_last_nbits ((Z.rem x 10)) (32)) (signed_last_nbits ((Z.rem x 10)) (32))) ” &&
  “ ((Z.quot x 10) <= x_pre) ” &&
  “ ((0 : Int) <= (Z.quot x 10)) ”
  &&  emp
)

noncomputable def step_entail_wit_2_1_split_goal_1 : Prop :=
  forall (x_pre : Int) (mx : Int) (mn : Int) (x : Int) (PreH1 : ((signed_last_nbits ((Z.rem x 10)) (32)) > mx)) (PreH2 : ((signed_last_nbits ((Z.rem x 10)) (32)) < mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : ((0 : Int) <= x)) (PreH6 : (x <= x_pre)) (PreH7 : ((0 : Int) <= mn)) (PreH8 : (mn <= 9)) (PreH9 : ((0 : Int) <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx)) (PreH12 : (x ≠ (0 : Int))) ,
  (DigitScanState x_pre (Z.quot x 10) (signed_last_nbits ((Z.rem x 10)) (32)) (signed_last_nbits ((Z.rem x 10)) (32)))

noncomputable def step_entail_wit_2_1_split_goal_2 : Prop :=
  forall (x_pre : Int) (mx : Int) (mn : Int) (x : Int) (PreH1 : ((signed_last_nbits ((Z.rem x 10)) (32)) > mx)) (PreH2 : ((signed_last_nbits ((Z.rem x 10)) (32)) < mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : ((0 : Int) <= x)) (PreH6 : (x <= x_pre)) (PreH7 : ((0 : Int) <= mn)) (PreH8 : (mn <= 9)) (PreH9 : ((0 : Int) <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx)) (PreH12 : (x ≠ (0 : Int))) ,
  ((Z.quot x 10) <= x_pre)

noncomputable def step_entail_wit_2_1_split_goal_3 : Prop :=
  forall (x_pre : Int) (mx : Int) (mn : Int) (x : Int) (PreH1 : ((signed_last_nbits ((Z.rem x 10)) (32)) > mx)) (PreH2 : ((signed_last_nbits ((Z.rem x 10)) (32)) < mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : ((0 : Int) <= x)) (PreH6 : (x <= x_pre)) (PreH7 : ((0 : Int) <= mn)) (PreH8 : (mn <= 9)) (PreH9 : ((0 : Int) <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx)) (PreH12 : (x ≠ (0 : Int))) ,
  ((0 : Int) <= (Z.quot x 10))

noncomputable def step_entail_wit_2_2 : Prop :=
  (
forall (x_pre : Int) (mx : Int) (mn : Int) (x : Int) (PreH1 : ((signed_last_nbits ((Z.rem x 10)) (32)) > mx)) (PreH2 : ((signed_last_nbits ((Z.rem x 10)) (32)) >= mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : ((0 : Int) <= x)) (PreH6 : (x <= x_pre)) (PreH7 : ((0 : Int) <= mn)) (PreH8 : (mn <= 9)) (PreH9 : ((0 : Int) <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx)) (PreH12 : (x ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (1 <= x_pre) ” &&
  “ (x_pre <= 1810000000000000000) ” &&
  “ ((0 : Int) <= (Z.quot x 10)) ” &&
  “ ((Z.quot x 10) <= x_pre) ” &&
  “ ((0 : Int) <= mn) ” &&
  “ (mn <= 9) ” &&
  “ ((0 : Int) <= (signed_last_nbits ((Z.rem x 10)) (32))) ” &&
  “ ((signed_last_nbits ((Z.rem x 10)) (32)) <= 9) ” &&
  “ (DigitScanState x_pre (Z.quot x 10) mn (signed_last_nbits ((Z.rem x 10)) (32))) ”
  &&  emp
) \/
(
forall (x_pre : Int) (mx : Int) (mn : Int) (x : Int) (PreH1 : ((signed_last_nbits ((Z.rem x 10)) (32)) > mx)) (PreH2 : ((signed_last_nbits ((Z.rem x 10)) (32)) >= mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : ((0 : Int) <= x)) (PreH6 : (x <= x_pre)) (PreH7 : ((0 : Int) <= mn)) (PreH8 : (mn <= 9)) (PreH9 : ((0 : Int) <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx)) (PreH12 : (x ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (DigitScanState x_pre (Z.quot x 10) mn (signed_last_nbits ((Z.rem x 10)) (32))) ” &&
  “ ((signed_last_nbits ((Z.rem x 10)) (32)) <= 9) ” &&
  “ ((Z.quot x 10) <= x_pre) ” &&
  “ ((0 : Int) <= (Z.quot x 10)) ”
  &&  emp
)

noncomputable def step_entail_wit_2_2_split_goal_1 : Prop :=
  forall (x_pre : Int) (mx : Int) (mn : Int) (x : Int) (PreH1 : ((signed_last_nbits ((Z.rem x 10)) (32)) > mx)) (PreH2 : ((signed_last_nbits ((Z.rem x 10)) (32)) >= mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : ((0 : Int) <= x)) (PreH6 : (x <= x_pre)) (PreH7 : ((0 : Int) <= mn)) (PreH8 : (mn <= 9)) (PreH9 : ((0 : Int) <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx)) (PreH12 : (x ≠ (0 : Int))) ,
  (DigitScanState x_pre (Z.quot x 10) mn (signed_last_nbits ((Z.rem x 10)) (32)))

noncomputable def step_entail_wit_2_2_split_goal_2 : Prop :=
  forall (x_pre : Int) (mx : Int) (mn : Int) (x : Int) (PreH1 : ((signed_last_nbits ((Z.rem x 10)) (32)) > mx)) (PreH2 : ((signed_last_nbits ((Z.rem x 10)) (32)) >= mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : ((0 : Int) <= x)) (PreH6 : (x <= x_pre)) (PreH7 : ((0 : Int) <= mn)) (PreH8 : (mn <= 9)) (PreH9 : ((0 : Int) <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx)) (PreH12 : (x ≠ (0 : Int))) ,
  ((signed_last_nbits ((Z.rem x 10)) (32)) <= 9)

noncomputable def step_entail_wit_2_2_split_goal_3 : Prop :=
  forall (x_pre : Int) (mx : Int) (mn : Int) (x : Int) (PreH1 : ((signed_last_nbits ((Z.rem x 10)) (32)) > mx)) (PreH2 : ((signed_last_nbits ((Z.rem x 10)) (32)) >= mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : ((0 : Int) <= x)) (PreH6 : (x <= x_pre)) (PreH7 : ((0 : Int) <= mn)) (PreH8 : (mn <= 9)) (PreH9 : ((0 : Int) <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx)) (PreH12 : (x ≠ (0 : Int))) ,
  ((Z.quot x 10) <= x_pre)

noncomputable def step_entail_wit_2_2_split_goal_4 : Prop :=
  forall (x_pre : Int) (mx : Int) (mn : Int) (x : Int) (PreH1 : ((signed_last_nbits ((Z.rem x 10)) (32)) > mx)) (PreH2 : ((signed_last_nbits ((Z.rem x 10)) (32)) >= mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : ((0 : Int) <= x)) (PreH6 : (x <= x_pre)) (PreH7 : ((0 : Int) <= mn)) (PreH8 : (mn <= 9)) (PreH9 : ((0 : Int) <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx)) (PreH12 : (x ≠ (0 : Int))) ,
  ((0 : Int) <= (Z.quot x 10))

noncomputable def step_entail_wit_2_3 : Prop :=
  (
forall (x_pre : Int) (mx : Int) (mn : Int) (x : Int) (PreH1 : ((signed_last_nbits ((Z.rem x 10)) (32)) <= mx)) (PreH2 : ((signed_last_nbits ((Z.rem x 10)) (32)) < mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : ((0 : Int) <= x)) (PreH6 : (x <= x_pre)) (PreH7 : ((0 : Int) <= mn)) (PreH8 : (mn <= 9)) (PreH9 : ((0 : Int) <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx)) (PreH12 : (x ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (1 <= x_pre) ” &&
  “ (x_pre <= 1810000000000000000) ” &&
  “ ((0 : Int) <= (Z.quot x 10)) ” &&
  “ ((Z.quot x 10) <= x_pre) ” &&
  “ ((0 : Int) <= (signed_last_nbits ((Z.rem x 10)) (32))) ” &&
  “ ((signed_last_nbits ((Z.rem x 10)) (32)) <= 9) ” &&
  “ ((0 : Int) <= mx) ” &&
  “ (mx <= 9) ” &&
  “ (DigitScanState x_pre (Z.quot x 10) (signed_last_nbits ((Z.rem x 10)) (32)) mx) ”
  &&  emp
) \/
(
forall (x_pre : Int) (mx : Int) (mn : Int) (x : Int) (PreH1 : ((signed_last_nbits ((Z.rem x 10)) (32)) <= mx)) (PreH2 : ((signed_last_nbits ((Z.rem x 10)) (32)) < mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : ((0 : Int) <= x)) (PreH6 : (x <= x_pre)) (PreH7 : ((0 : Int) <= mn)) (PreH8 : (mn <= 9)) (PreH9 : ((0 : Int) <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx)) (PreH12 : (x ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (DigitScanState x_pre (Z.quot x 10) (signed_last_nbits ((Z.rem x 10)) (32)) mx) ” &&
  “ ((0 : Int) <= (signed_last_nbits ((Z.rem x 10)) (32))) ” &&
  “ ((Z.quot x 10) <= x_pre) ” &&
  “ ((0 : Int) <= (Z.quot x 10)) ”
  &&  emp
)

noncomputable def step_entail_wit_2_3_split_goal_1 : Prop :=
  forall (x_pre : Int) (mx : Int) (mn : Int) (x : Int) (PreH1 : ((signed_last_nbits ((Z.rem x 10)) (32)) <= mx)) (PreH2 : ((signed_last_nbits ((Z.rem x 10)) (32)) < mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : ((0 : Int) <= x)) (PreH6 : (x <= x_pre)) (PreH7 : ((0 : Int) <= mn)) (PreH8 : (mn <= 9)) (PreH9 : ((0 : Int) <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx)) (PreH12 : (x ≠ (0 : Int))) ,
  (DigitScanState x_pre (Z.quot x 10) (signed_last_nbits ((Z.rem x 10)) (32)) mx)

noncomputable def step_entail_wit_2_3_split_goal_2 : Prop :=
  forall (x_pre : Int) (mx : Int) (mn : Int) (x : Int) (PreH1 : ((signed_last_nbits ((Z.rem x 10)) (32)) <= mx)) (PreH2 : ((signed_last_nbits ((Z.rem x 10)) (32)) < mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : ((0 : Int) <= x)) (PreH6 : (x <= x_pre)) (PreH7 : ((0 : Int) <= mn)) (PreH8 : (mn <= 9)) (PreH9 : ((0 : Int) <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx)) (PreH12 : (x ≠ (0 : Int))) ,
  ((0 : Int) <= (signed_last_nbits ((Z.rem x 10)) (32)))

noncomputable def step_entail_wit_2_3_split_goal_3 : Prop :=
  forall (x_pre : Int) (mx : Int) (mn : Int) (x : Int) (PreH1 : ((signed_last_nbits ((Z.rem x 10)) (32)) <= mx)) (PreH2 : ((signed_last_nbits ((Z.rem x 10)) (32)) < mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : ((0 : Int) <= x)) (PreH6 : (x <= x_pre)) (PreH7 : ((0 : Int) <= mn)) (PreH8 : (mn <= 9)) (PreH9 : ((0 : Int) <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx)) (PreH12 : (x ≠ (0 : Int))) ,
  ((Z.quot x 10) <= x_pre)

noncomputable def step_entail_wit_2_3_split_goal_4 : Prop :=
  forall (x_pre : Int) (mx : Int) (mn : Int) (x : Int) (PreH1 : ((signed_last_nbits ((Z.rem x 10)) (32)) <= mx)) (PreH2 : ((signed_last_nbits ((Z.rem x 10)) (32)) < mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : ((0 : Int) <= x)) (PreH6 : (x <= x_pre)) (PreH7 : ((0 : Int) <= mn)) (PreH8 : (mn <= 9)) (PreH9 : ((0 : Int) <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx)) (PreH12 : (x ≠ (0 : Int))) ,
  ((0 : Int) <= (Z.quot x 10))

noncomputable def step_entail_wit_2_4 : Prop :=
  (
forall (x_pre : Int) (mx : Int) (mn : Int) (x : Int) (PreH1 : ((signed_last_nbits ((Z.rem x 10)) (32)) <= mx)) (PreH2 : ((signed_last_nbits ((Z.rem x 10)) (32)) >= mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : ((0 : Int) <= x)) (PreH6 : (x <= x_pre)) (PreH7 : ((0 : Int) <= mn)) (PreH8 : (mn <= 9)) (PreH9 : ((0 : Int) <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx)) (PreH12 : (x ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (1 <= x_pre) ” &&
  “ (x_pre <= 1810000000000000000) ” &&
  “ ((0 : Int) <= (Z.quot x 10)) ” &&
  “ ((Z.quot x 10) <= x_pre) ” &&
  “ ((0 : Int) <= mn) ” &&
  “ (mn <= 9) ” &&
  “ ((0 : Int) <= mx) ” &&
  “ (mx <= 9) ” &&
  “ (DigitScanState x_pre (Z.quot x 10) mn mx) ”
  &&  emp
) \/
(
forall (x_pre : Int) (mx : Int) (mn : Int) (x : Int) (PreH1 : ((signed_last_nbits ((Z.rem x 10)) (32)) <= mx)) (PreH2 : ((signed_last_nbits ((Z.rem x 10)) (32)) >= mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : ((0 : Int) <= x)) (PreH6 : (x <= x_pre)) (PreH7 : ((0 : Int) <= mn)) (PreH8 : (mn <= 9)) (PreH9 : ((0 : Int) <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx)) (PreH12 : (x ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (DigitScanState x_pre (Z.quot x 10) mn mx) ” &&
  “ ((Z.quot x 10) <= x_pre) ” &&
  “ ((0 : Int) <= (Z.quot x 10)) ”
  &&  emp
)

noncomputable def step_entail_wit_2_4_split_goal_1 : Prop :=
  forall (x_pre : Int) (mx : Int) (mn : Int) (x : Int) (PreH1 : ((signed_last_nbits ((Z.rem x 10)) (32)) <= mx)) (PreH2 : ((signed_last_nbits ((Z.rem x 10)) (32)) >= mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : ((0 : Int) <= x)) (PreH6 : (x <= x_pre)) (PreH7 : ((0 : Int) <= mn)) (PreH8 : (mn <= 9)) (PreH9 : ((0 : Int) <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx)) (PreH12 : (x ≠ (0 : Int))) ,
  (DigitScanState x_pre (Z.quot x 10) mn mx)

noncomputable def step_entail_wit_2_4_split_goal_2 : Prop :=
  forall (x_pre : Int) (mx : Int) (mn : Int) (x : Int) (PreH1 : ((signed_last_nbits ((Z.rem x 10)) (32)) <= mx)) (PreH2 : ((signed_last_nbits ((Z.rem x 10)) (32)) >= mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : ((0 : Int) <= x)) (PreH6 : (x <= x_pre)) (PreH7 : ((0 : Int) <= mn)) (PreH8 : (mn <= 9)) (PreH9 : ((0 : Int) <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx)) (PreH12 : (x ≠ (0 : Int))) ,
  ((Z.quot x 10) <= x_pre)

noncomputable def step_entail_wit_2_4_split_goal_3 : Prop :=
  forall (x_pre : Int) (mx : Int) (mn : Int) (x : Int) (PreH1 : ((signed_last_nbits ((Z.rem x 10)) (32)) <= mx)) (PreH2 : ((signed_last_nbits ((Z.rem x 10)) (32)) >= mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : ((0 : Int) <= x)) (PreH6 : (x <= x_pre)) (PreH7 : ((0 : Int) <= mn)) (PreH8 : (mn <= 9)) (PreH9 : ((0 : Int) <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx)) (PreH12 : (x ≠ (0 : Int))) ,
  ((0 : Int) <= (Z.quot x 10))

noncomputable def step_return_wit_1 : Prop :=
  (
forall (x_pre : Int) (mx : Int) (mn : Int) (x : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1810000000000000000)) (PreH3 : ((0 : Int) <= x)) (PreH4 : (x <= x_pre)) (PreH5 : ((0 : Int) <= mn)) (PreH6 : (mn <= 9)) (PreH7 : ((0 : Int) <= mx)) (PreH8 : (mx <= 9)) (PreH9 : (DigitScanState x_pre x mn mx)) (PreH10 : (x = (0 : Int))) ,
  TT && emp 
|--
  “ ((0 : Int) <= (mn * mx)) ” &&
  “ ((mn * mx) <= 81) ” &&
  “ (DigitRecurrenceStep x_pre (x_pre + (mn * mx))) ”
  &&  emp
) \/
(
forall (x_pre : Int) (mx : Int) (mn : Int) (x : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1810000000000000000)) (PreH3 : ((0 : Int) <= x)) (PreH4 : (x <= x_pre)) (PreH5 : ((0 : Int) <= mn)) (PreH6 : (mn <= 9)) (PreH7 : ((0 : Int) <= mx)) (PreH8 : (mx <= 9)) (PreH9 : (DigitScanState x_pre x mn mx)) (PreH10 : (x = (0 : Int))) ,
  TT && emp 
|--
  “ (DigitRecurrenceStep x_pre (x_pre + (mn * mx))) ”
  &&  emp
)

noncomputable def step_return_wit_1_split_goal_1 : Prop :=
  forall (x_pre : Int) (mx : Int) (mn : Int) (x : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1810000000000000000)) (PreH3 : ((0 : Int) <= x)) (PreH4 : (x <= x_pre)) (PreH5 : ((0 : Int) <= mn)) (PreH6 : (mn <= 9)) (PreH7 : ((0 : Int) <= mx)) (PreH8 : (mx <= 9)) (PreH9 : (DigitScanState x_pre x mn mx)) (PreH10 : (x = (0 : Int))) ,
  (DigitRecurrenceStep x_pre (x_pre + (mn * mx)))

noncomputable def solver_safety_wit_1 : Prop :=
  forall (a1 : Int) (a_pre : Int) (k_pre : Int) (PreH1 : (1 <= a1)) (PreH2 : (a1 <= 1000000000000000000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 10000000000000000)) (PreH5 : (a_pre = a1)) ,
  ((( &( "i" ) )) # Int64 |->_)
  ** ((( &( "a" ) )) # Int64 |-> (a_pre))
  ** ((( &( "k" ) )) # Int64 |-> (k_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (a1 : Int) (a_pre : Int) (k_pre : Int) (a : Int) (i : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval <= 81)) (PreH4 : (DigitRecurrenceStep a (a + retval))) (PreH5 : (i < k_pre)) (PreH6 : (a_pre = a1)) (PreH7 : (1 <= a1)) (PreH8 : (a1 <= 1000000000000000000)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 10000000000000000)) (PreH11 : (1 <= i)) (PreH12 : (i <= k_pre)) (PreH13 : (a1 <= a)) (PreH14 : (a <= (a1 + (81 * (i - 1))))) (PreH15 : (a <= 1810000000000000000)) (PreH16 : (SequencePrefix a1 i a)) ,
  ((( &( "add" ) )) # Int64 |-> (retval))
  ** ((( &( "k" ) )) # Int64 |-> (k_pre))
  ** ((( &( "i" ) )) # Int64 |-> (i))
  ** ((( &( "a" ) )) # Int64 |-> (a))
|--
  “ ((a + retval) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (a + retval)) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (a1 : Int) (a_pre : Int) (k_pre : Int) (a : Int) (i : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval <= 81)) (PreH4 : (DigitRecurrenceStep a (a + retval))) (PreH5 : (i < k_pre)) (PreH6 : (a_pre = a1)) (PreH7 : (1 <= a1)) (PreH8 : (a1 <= 1000000000000000000)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 10000000000000000)) (PreH11 : (1 <= i)) (PreH12 : (i <= k_pre)) (PreH13 : (a1 <= a)) (PreH14 : (a <= (a1 + (81 * (i - 1))))) (PreH15 : (a <= 1810000000000000000)) (PreH16 : (SequencePrefix a1 i a)) ,
  ((( &( "k" ) )) # Int64 |-> (k_pre))
  ** ((( &( "i" ) )) # Int64 |-> (i))
  ** ((( &( "a" ) )) # Int64 |-> ((a + retval)))
|--
  “ ((i + 1) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (i + 1)) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (a1 : Int) (a_pre : Int) (k_pre : Int) (PreH1 : (1 <= a1)) (PreH2 : (a1 <= 1000000000000000000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 10000000000000000)) (PreH5 : (a_pre = a1)) ,
  TT && emp 
|--
  “ (a_pre = a1) ” &&
  “ (1 <= a1) ” &&
  “ (a1 <= 1000000000000000000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 10000000000000000) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= k_pre) ” &&
  “ (a1 <= a_pre) ” &&
  “ (a_pre <= (a1 + (81 * (1 - 1)))) ” &&
  “ (a_pre <= 1810000000000000000) ” &&
  “ (SequencePrefix a1 1 a_pre) ”
  &&  emp
) \/
(
forall (a1 : Int) (a_pre : Int) (k_pre : Int) (PreH1 : (1 <= a1)) (PreH2 : (a1 <= 1000000000000000000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 10000000000000000)) (PreH5 : (a_pre = a1)) ,
  TT && emp 
|--
  “ (SequencePrefix a1 1 a1) ”
  &&  emp
)

noncomputable def solver_entail_wit_1_split_goal_1 : Prop :=
  forall (a1 : Int) (a_pre : Int) (k_pre : Int) (PreH1 : (1 <= a1)) (PreH2 : (a1 <= 1000000000000000000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 10000000000000000)) (PreH5 : (a_pre = a1)) ,
  (SequencePrefix a1 1 a1)

noncomputable def solver_entail_wit_2 : Prop :=
  (
forall (a1 : Int) (a_pre : Int) (k_pre : Int) (a : Int) (i : Int) (retval : Int) (PreH1 : (retval = (0 : Int))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval <= 81)) (PreH4 : (DigitRecurrenceStep a (a + retval))) (PreH5 : (i < k_pre)) (PreH6 : (a_pre = a1)) (PreH7 : (1 <= a1)) (PreH8 : (a1 <= 1000000000000000000)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 10000000000000000)) (PreH11 : (1 <= i)) (PreH12 : (i <= k_pre)) (PreH13 : (a1 <= a)) (PreH14 : (a <= (a1 + (81 * (i - 1))))) (PreH15 : (a <= 1810000000000000000)) (PreH16 : (SequencePrefix a1 i a)) ,
  TT && emp 
|--
  “ (a_pre = a1) ” &&
  “ (1 <= a1) ” &&
  “ (a1 <= 1000000000000000000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 10000000000000000) ” &&
  “ (1 <= i) ” &&
  “ (i < k_pre) ” &&
  “ (retval = (0 : Int)) ” &&
  “ (a1 <= a) ” &&
  “ (a <= (a1 + (81 * (i - 1)))) ” &&
  “ (a <= 1810000000000000000) ” &&
  “ (SequencePrefix a1 i a) ” &&
  “ (Spec a1 k_pre a) ”
  &&  emp
) \/
(
forall (a1 : Int) (a_pre : Int) (k_pre : Int) (a : Int) (i : Int) (retval : Int) (PreH1 : (retval = (0 : Int))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval <= 81)) (PreH4 : (DigitRecurrenceStep a (a + retval))) (PreH5 : (i < k_pre)) (PreH6 : (a_pre = a1)) (PreH7 : (1 <= a1)) (PreH8 : (a1 <= 1000000000000000000)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 10000000000000000)) (PreH11 : (1 <= i)) (PreH12 : (i <= k_pre)) (PreH13 : (a1 <= a)) (PreH14 : (a <= (a1 + (81 * (i - 1))))) (PreH15 : (a <= 1810000000000000000)) (PreH16 : (SequencePrefix a1 i a)) ,
  TT && emp 
|--
  “ (Spec a1 k_pre a) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_split_goal_1 : Prop :=
  forall (a1 : Int) (a_pre : Int) (k_pre : Int) (a : Int) (i : Int) (retval : Int) (PreH1 : (retval = (0 : Int))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval <= 81)) (PreH4 : (DigitRecurrenceStep a (a + retval))) (PreH5 : (i < k_pre)) (PreH6 : (a_pre = a1)) (PreH7 : (1 <= a1)) (PreH8 : (a1 <= 1000000000000000000)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 10000000000000000)) (PreH11 : (1 <= i)) (PreH12 : (i <= k_pre)) (PreH13 : (a1 <= a)) (PreH14 : (a <= (a1 + (81 * (i - 1))))) (PreH15 : (a <= 1810000000000000000)) (PreH16 : (SequencePrefix a1 i a)) ,
  (Spec a1 k_pre a)

noncomputable def solver_entail_wit_3 : Prop :=
  (
forall (a1 : Int) (a_pre : Int) (k_pre : Int) (a : Int) (i : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval <= 81)) (PreH4 : (DigitRecurrenceStep a (a + retval))) (PreH5 : (i < k_pre)) (PreH6 : (a_pre = a1)) (PreH7 : (1 <= a1)) (PreH8 : (a1 <= 1000000000000000000)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 10000000000000000)) (PreH11 : (1 <= i)) (PreH12 : (i <= k_pre)) (PreH13 : (a1 <= a)) (PreH14 : (a <= (a1 + (81 * (i - 1))))) (PreH15 : (a <= 1810000000000000000)) (PreH16 : (SequencePrefix a1 i a)) ,
  TT && emp 
|--
  “ (a_pre = a1) ” &&
  “ (1 <= a1) ” &&
  “ (a1 <= 1000000000000000000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 10000000000000000) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= k_pre) ” &&
  “ (a1 <= (a + retval)) ” &&
  “ ((a + retval) <= (a1 + (81 * ((i + 1) - 1)))) ” &&
  “ ((a + retval) <= 1810000000000000000) ” &&
  “ (SequencePrefix a1 (i + 1) (a + retval)) ”
  &&  emp
) \/
(
forall (a1 : Int) (a_pre : Int) (k_pre : Int) (a : Int) (i : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval <= 81)) (PreH4 : (DigitRecurrenceStep a (a + retval))) (PreH5 : (i < k_pre)) (PreH6 : (a_pre = a1)) (PreH7 : (1 <= a1)) (PreH8 : (a1 <= 1000000000000000000)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 10000000000000000)) (PreH11 : (1 <= i)) (PreH12 : (i <= k_pre)) (PreH13 : (a1 <= a)) (PreH14 : (a <= (a1 + (81 * (i - 1))))) (PreH15 : (a <= 1810000000000000000)) (PreH16 : (SequencePrefix a1 i a)) ,
  TT && emp 
|--
  “ (SequencePrefix a1 (i + 1) (a + retval)) ”
  &&  emp
)

noncomputable def solver_entail_wit_3_split_goal_1 : Prop :=
  forall (a1 : Int) (a_pre : Int) (k_pre : Int) (a : Int) (i : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval <= 81)) (PreH4 : (DigitRecurrenceStep a (a + retval))) (PreH5 : (i < k_pre)) (PreH6 : (a_pre = a1)) (PreH7 : (1 <= a1)) (PreH8 : (a1 <= 1000000000000000000)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 10000000000000000)) (PreH11 : (1 <= i)) (PreH12 : (i <= k_pre)) (PreH13 : (a1 <= a)) (PreH14 : (a <= (a1 + (81 * (i - 1))))) (PreH15 : (a <= 1810000000000000000)) (PreH16 : (SequencePrefix a1 i a)) ,
  (SequencePrefix a1 (i + 1) (a + retval))

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (a1 : Int) (a_pre : Int) (k_pre : Int) (a : Int) (i : Int) (PreH1 : (i >= k_pre)) (PreH2 : (a_pre = a1)) (PreH3 : (1 <= a1)) (PreH4 : (a1 <= 1000000000000000000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 10000000000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= k_pre)) (PreH9 : (a1 <= a)) (PreH10 : (a <= (a1 + (81 * (i - 1))))) (PreH11 : (a <= 1810000000000000000)) (PreH12 : (SequencePrefix a1 i a)) ,
  TT && emp 
|--
  “ (Spec a1 k_pre a) ”
  &&  emp
) \/
(
forall (a1 : Int) (a_pre : Int) (k_pre : Int) (a : Int) (i : Int) (PreH1 : (i >= k_pre)) (PreH2 : (a_pre = a1)) (PreH3 : (1 <= a1)) (PreH4 : (a1 <= 1000000000000000000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 10000000000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= k_pre)) (PreH9 : (a1 <= a)) (PreH10 : (a <= (a1 + (81 * (i - 1))))) (PreH11 : (a <= 1810000000000000000)) (PreH12 : (SequencePrefix a1 i a)) ,
  TT && emp 
|--
  “ (Spec a1 k_pre a) ”
  &&  emp
)

noncomputable def solver_return_wit_1_split_goal_1 : Prop :=
  forall (a1 : Int) (a_pre : Int) (k_pre : Int) (a : Int) (i : Int) (PreH1 : (i >= k_pre)) (PreH2 : (a_pre = a1)) (PreH3 : (1 <= a1)) (PreH4 : (a1 <= 1000000000000000000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 10000000000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= k_pre)) (PreH9 : (a1 <= a)) (PreH10 : (a <= (a1 + (81 * (i - 1))))) (PreH11 : (a <= 1810000000000000000)) (PreH12 : (SequencePrefix a1 i a)) ,
  (Spec a1 k_pre a)

noncomputable def solver_return_wit_2 : Prop :=
  forall (a1 : Int) (a_pre : Int) (k_pre : Int) (i : Int) (add : Int) (a : Int) (PreH1 : (a_pre = a1)) (PreH2 : (1 <= a1)) (PreH3 : (a1 <= 1000000000000000000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 10000000000000000)) (PreH6 : (1 <= i)) (PreH7 : (i < k_pre)) (PreH8 : (add = (0 : Int))) (PreH9 : (a1 <= a)) (PreH10 : (a <= (a1 + (81 * (i - 1))))) (PreH11 : (a <= 1810000000000000000)) (PreH12 : (SequencePrefix a1 i a)) (PreH13 : (Spec a1 k_pre a)) ,
  TT && emp 
|--
  “ (Spec a1 k_pre a) ”
  &&  emp

noncomputable def solver_partial_solve_wit_1_pure : Prop :=
  forall (a1 : Int) (a_pre : Int) (k_pre : Int) (a : Int) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (a_pre = a1)) (PreH3 : (1 <= a1)) (PreH4 : (a1 <= 1000000000000000000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 10000000000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= k_pre)) (PreH9 : (a1 <= a)) (PreH10 : (a <= (a1 + (81 * (i - 1))))) (PreH11 : (a <= 1810000000000000000)) (PreH12 : (SequencePrefix a1 i a)) ,
  ((( &( "add" ) )) # Int64 |->_)
  ** ((( &( "k" ) )) # Int64 |-> (k_pre))
  ** ((( &( "i" ) )) # Int64 |-> (i))
  ** ((( &( "a" ) )) # Int64 |-> (a))
|--
  “ (1 <= a) ” &&
  “ (a <= 1810000000000000000) ”

noncomputable def solver_partial_solve_wit_1_aux : Prop :=
  forall (a1 : Int) (a_pre : Int) (k_pre : Int) (a : Int) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (a_pre = a1)) (PreH3 : (1 <= a1)) (PreH4 : (a1 <= 1000000000000000000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 10000000000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= k_pre)) (PreH9 : (a1 <= a)) (PreH10 : (a <= (a1 + (81 * (i - 1))))) (PreH11 : (a <= 1810000000000000000)) (PreH12 : (SequencePrefix a1 i a)) ,
  TT && emp 
|--
  “ (1 <= a) ” &&
  “ (a <= 1810000000000000000) ” &&
  “ (i < k_pre) ” &&
  “ (a_pre = a1) ” &&
  “ (1 <= a1) ” &&
  “ (a1 <= 1000000000000000000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 10000000000000000) ” &&
  “ (1 <= i) ” &&
  “ (i <= k_pre) ” &&
  “ (a1 <= a) ” &&
  “ (a <= (a1 + (81 * (i - 1)))) ” &&
  “ (a <= 1810000000000000000) ” &&
  “ (SequencePrefix a1 i a) ”
  &&  emp

noncomputable def solver_partial_solve_wit_1 : Prop := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux


structure VC_Correct : Type where
  proof_of_step_safety_wit_1 : step_safety_wit_1
  proof_of_step_safety_wit_2 : step_safety_wit_2
  proof_of_step_safety_wit_3 : step_safety_wit_3
  proof_of_step_safety_wit_4 : step_safety_wit_4
  proof_of_step_safety_wit_5 : step_safety_wit_5
  proof_of_step_safety_wit_6 : step_safety_wit_6
  proof_of_step_safety_wit_7 : step_safety_wit_7
  proof_of_solver_safety_wit_1 : solver_safety_wit_1
  proof_of_solver_safety_wit_2 : solver_safety_wit_2
  proof_of_solver_safety_wit_3 : solver_safety_wit_3
  proof_of_solver_return_wit_2 : solver_return_wit_2
  proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_step_entail_wit_1 : step_entail_wit_1
  proof_of_step_entail_wit_2_1 : step_entail_wit_2_1
  proof_of_step_entail_wit_2_2 : step_entail_wit_2_2
  proof_of_step_entail_wit_2_3 : step_entail_wit_2_3
  proof_of_step_entail_wit_2_4 : step_entail_wit_2_4
  proof_of_step_return_wit_1 : step_return_wit_1
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_2 : solver_entail_wit_2
  proof_of_solver_entail_wit_3 : solver_entail_wit_3
  proof_of_solver_return_wit_1 : solver_return_wit_1

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P026_1355A_sequence_with_digits_goal
