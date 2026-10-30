import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P044_837C_two_seals_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P044_837C_two_seals_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P044_837C_two_seals_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P044_837C_two_seals_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def fits_safety_wit_1 : Prop :=
  forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (1 <= w1_pre)) (PreH2 : (w1_pre <= 100)) (PreH3 : (1 <= h1_pre)) (PreH4 : (h1_pre <= 100)) (PreH5 : (1 <= w2_pre)) (PreH6 : (w2_pre <= 100)) (PreH7 : (1 <= h2_pre)) (PreH8 : (h2_pre <= 100)) (PreH9 : (1 <= a_pre)) (PreH10 : (a_pre <= 100)) (PreH11 : (1 <= b_pre)) (PreH12 : (b_pre <= 100)) ,
  ((( &( "w1" ) )) # Int |-> (w1_pre))
  ** ((( &( "h1" ) )) # Int |-> (h1_pre))
  ** ((( &( "w2" ) )) # Int |-> (w2_pre))
  ** ((( &( "h2" ) )) # Int |-> (h2_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
|--
  “ ((w1_pre + w2_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (w1_pre + w2_pre)) ”

noncomputable def fits_safety_wit_2 : Prop :=
  forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (h2_pre <= b_pre)) (PreH2 : (h1_pre <= h2_pre)) (PreH3 : ((w1_pre + w2_pre) <= a_pre)) (PreH4 : (1 <= w1_pre)) (PreH5 : (w1_pre <= 100)) (PreH6 : (1 <= h1_pre)) (PreH7 : (h1_pre <= 100)) (PreH8 : (1 <= w2_pre)) (PreH9 : (w2_pre <= 100)) (PreH10 : (1 <= h2_pre)) (PreH11 : (h2_pre <= 100)) (PreH12 : (1 <= a_pre)) (PreH13 : (a_pre <= 100)) (PreH14 : (1 <= b_pre)) (PreH15 : (b_pre <= 100)) ,
  ((( &( "w1" ) )) # Int |-> (w1_pre))
  ** ((( &( "h1" ) )) # Int |-> (h1_pre))
  ** ((( &( "w2" ) )) # Int |-> (w2_pre))
  ** ((( &( "h2" ) )) # Int |-> (h2_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def fits_safety_wit_3 : Prop :=
  forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (h1_pre <= b_pre)) (PreH2 : (h1_pre > h2_pre)) (PreH3 : ((w1_pre + w2_pre) <= a_pre)) (PreH4 : (1 <= w1_pre)) (PreH5 : (w1_pre <= 100)) (PreH6 : (1 <= h1_pre)) (PreH7 : (h1_pre <= 100)) (PreH8 : (1 <= w2_pre)) (PreH9 : (w2_pre <= 100)) (PreH10 : (1 <= h2_pre)) (PreH11 : (h2_pre <= 100)) (PreH12 : (1 <= a_pre)) (PreH13 : (a_pre <= 100)) (PreH14 : (1 <= b_pre)) (PreH15 : (b_pre <= 100)) ,
  ((( &( "w1" ) )) # Int |-> (w1_pre))
  ** ((( &( "h1" ) )) # Int |-> (h1_pre))
  ** ((( &( "w2" ) )) # Int |-> (w2_pre))
  ** ((( &( "h2" ) )) # Int |-> (h2_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def fits_safety_wit_4 : Prop :=
  forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (h1_pre > b_pre)) (PreH2 : (h1_pre > h2_pre)) (PreH3 : ((w1_pre + w2_pre) <= a_pre)) (PreH4 : (1 <= w1_pre)) (PreH5 : (w1_pre <= 100)) (PreH6 : (1 <= h1_pre)) (PreH7 : (h1_pre <= 100)) (PreH8 : (1 <= w2_pre)) (PreH9 : (w2_pre <= 100)) (PreH10 : (1 <= h2_pre)) (PreH11 : (h2_pre <= 100)) (PreH12 : (1 <= a_pre)) (PreH13 : (a_pre <= 100)) (PreH14 : (1 <= b_pre)) (PreH15 : (b_pre <= 100)) ,
  ((( &( "w1" ) )) # Int |-> (w1_pre))
  ** ((( &( "h1" ) )) # Int |-> (h1_pre))
  ** ((( &( "w2" ) )) # Int |-> (w2_pre))
  ** ((( &( "h2" ) )) # Int |-> (h2_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
|--
  “ ((h1_pre + h2_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (h1_pre + h2_pre)) ”

noncomputable def fits_safety_wit_5 : Prop :=
  forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (h2_pre > b_pre)) (PreH2 : (h1_pre <= h2_pre)) (PreH3 : ((w1_pre + w2_pre) <= a_pre)) (PreH4 : (1 <= w1_pre)) (PreH5 : (w1_pre <= 100)) (PreH6 : (1 <= h1_pre)) (PreH7 : (h1_pre <= 100)) (PreH8 : (1 <= w2_pre)) (PreH9 : (w2_pre <= 100)) (PreH10 : (1 <= h2_pre)) (PreH11 : (h2_pre <= 100)) (PreH12 : (1 <= a_pre)) (PreH13 : (a_pre <= 100)) (PreH14 : (1 <= b_pre)) (PreH15 : (b_pre <= 100)) ,
  ((( &( "w1" ) )) # Int |-> (w1_pre))
  ** ((( &( "h1" ) )) # Int |-> (h1_pre))
  ** ((( &( "w2" ) )) # Int |-> (w2_pre))
  ** ((( &( "h2" ) )) # Int |-> (h2_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
|--
  “ ((h1_pre + h2_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (h1_pre + h2_pre)) ”

noncomputable def fits_safety_wit_6 : Prop :=
  forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : ((w1_pre + w2_pre) > a_pre)) (PreH2 : (1 <= w1_pre)) (PreH3 : (w1_pre <= 100)) (PreH4 : (1 <= h1_pre)) (PreH5 : (h1_pre <= 100)) (PreH6 : (1 <= w2_pre)) (PreH7 : (w2_pre <= 100)) (PreH8 : (1 <= h2_pre)) (PreH9 : (h2_pre <= 100)) (PreH10 : (1 <= a_pre)) (PreH11 : (a_pre <= 100)) (PreH12 : (1 <= b_pre)) (PreH13 : (b_pre <= 100)) ,
  ((( &( "w1" ) )) # Int |-> (w1_pre))
  ** ((( &( "h1" ) )) # Int |-> (h1_pre))
  ** ((( &( "w2" ) )) # Int |-> (w2_pre))
  ** ((( &( "h2" ) )) # Int |-> (h2_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
|--
  “ ((h1_pre + h2_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (h1_pre + h2_pre)) ”

noncomputable def fits_safety_wit_7 : Prop :=
  forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : ((h1_pre + h2_pre) <= b_pre)) (PreH2 : (h2_pre > b_pre)) (PreH3 : (h1_pre <= h2_pre)) (PreH4 : ((w1_pre + w2_pre) <= a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  ((( &( "w1" ) )) # Int |-> (w1_pre))
  ** ((( &( "h1" ) )) # Int |-> (h1_pre))
  ** ((( &( "w2" ) )) # Int |-> (w2_pre))
  ** ((( &( "h2" ) )) # Int |-> (h2_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
|--
  “ False ”

noncomputable def fits_safety_wit_8 : Prop :=
  forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : ((h1_pre + h2_pre) <= b_pre)) (PreH2 : (h1_pre > b_pre)) (PreH3 : (h1_pre > h2_pre)) (PreH4 : ((w1_pre + w2_pre) <= a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  ((( &( "w1" ) )) # Int |-> (w1_pre))
  ** ((( &( "h1" ) )) # Int |-> (h1_pre))
  ** ((( &( "w2" ) )) # Int |-> (w2_pre))
  ** ((( &( "h2" ) )) # Int |-> (h2_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
|--
  “ False ”

noncomputable def fits_safety_wit_9 : Prop :=
  forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (w2_pre <= a_pre)) (PreH2 : (w1_pre <= w2_pre)) (PreH3 : ((h1_pre + h2_pre) <= b_pre)) (PreH4 : ((w1_pre + w2_pre) > a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  ((( &( "w1" ) )) # Int |-> (w1_pre))
  ** ((( &( "h1" ) )) # Int |-> (h1_pre))
  ** ((( &( "w2" ) )) # Int |-> (w2_pre))
  ** ((( &( "h2" ) )) # Int |-> (h2_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def fits_safety_wit_10 : Prop :=
  forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (w1_pre <= a_pre)) (PreH2 : (w1_pre > w2_pre)) (PreH3 : ((h1_pre + h2_pre) <= b_pre)) (PreH4 : ((w1_pre + w2_pre) > a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  ((( &( "w1" ) )) # Int |-> (w1_pre))
  ** ((( &( "h1" ) )) # Int |-> (h1_pre))
  ** ((( &( "w2" ) )) # Int |-> (w2_pre))
  ** ((( &( "h2" ) )) # Int |-> (h2_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def fits_safety_wit_11 : Prop :=
  forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : ((h1_pre + h2_pre) > b_pre)) (PreH2 : (h1_pre > b_pre)) (PreH3 : (h1_pre > h2_pre)) (PreH4 : ((w1_pre + w2_pre) <= a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  ((( &( "w1" ) )) # Int |-> (w1_pre))
  ** ((( &( "h1" ) )) # Int |-> (h1_pre))
  ** ((( &( "w2" ) )) # Int |-> (w2_pre))
  ** ((( &( "h2" ) )) # Int |-> (h2_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def fits_safety_wit_12 : Prop :=
  forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : ((h1_pre + h2_pre) > b_pre)) (PreH2 : (h2_pre > b_pre)) (PreH3 : (h1_pre <= h2_pre)) (PreH4 : ((w1_pre + w2_pre) <= a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  ((( &( "w1" ) )) # Int |-> (w1_pre))
  ** ((( &( "h1" ) )) # Int |-> (h1_pre))
  ** ((( &( "w2" ) )) # Int |-> (w2_pre))
  ** ((( &( "h2" ) )) # Int |-> (h2_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def fits_safety_wit_13 : Prop :=
  forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : ((h1_pre + h2_pre) > b_pre)) (PreH2 : ((w1_pre + w2_pre) > a_pre)) (PreH3 : (1 <= w1_pre)) (PreH4 : (w1_pre <= 100)) (PreH5 : (1 <= h1_pre)) (PreH6 : (h1_pre <= 100)) (PreH7 : (1 <= w2_pre)) (PreH8 : (w2_pre <= 100)) (PreH9 : (1 <= h2_pre)) (PreH10 : (h2_pre <= 100)) (PreH11 : (1 <= a_pre)) (PreH12 : (a_pre <= 100)) (PreH13 : (1 <= b_pre)) (PreH14 : (b_pre <= 100)) ,
  ((( &( "w1" ) )) # Int |-> (w1_pre))
  ** ((( &( "h1" ) )) # Int |-> (h1_pre))
  ** ((( &( "w2" ) )) # Int |-> (w2_pre))
  ** ((( &( "h2" ) )) # Int |-> (h2_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def fits_safety_wit_14 : Prop :=
  forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (w2_pre > a_pre)) (PreH2 : (w1_pre <= w2_pre)) (PreH3 : ((h1_pre + h2_pre) <= b_pre)) (PreH4 : ((w1_pre + w2_pre) > a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  ((( &( "w1" ) )) # Int |-> (w1_pre))
  ** ((( &( "h1" ) )) # Int |-> (h1_pre))
  ** ((( &( "w2" ) )) # Int |-> (w2_pre))
  ** ((( &( "h2" ) )) # Int |-> (h2_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def fits_safety_wit_15 : Prop :=
  forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (w1_pre > a_pre)) (PreH2 : (w1_pre > w2_pre)) (PreH3 : ((h1_pre + h2_pre) <= b_pre)) (PreH4 : ((w1_pre + w2_pre) > a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  ((( &( "w1" ) )) # Int |-> (w1_pre))
  ** ((( &( "h1" ) )) # Int |-> (h1_pre))
  ** ((( &( "w2" ) )) # Int |-> (w2_pre))
  ** ((( &( "h2" ) )) # Int |-> (h2_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def fits_return_wit_1 : Prop :=
  (
forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : ((h1_pre + h2_pre) > b_pre)) (PreH2 : (h1_pre > b_pre)) (PreH3 : (h1_pre > h2_pre)) (PreH4 : ((w1_pre + w2_pre) <= a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  TT && emp 
|--
  “ ((0 : Int) = (0 : Int)) ” &&
  “ ¬((FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre)) ”
  &&  emp
) \/
(
forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : ((h1_pre + h2_pre) > b_pre)) (PreH2 : (h1_pre > b_pre)) (PreH3 : (h1_pre > h2_pre)) (PreH4 : ((w1_pre + w2_pre) <= a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  TT && emp 
|--
  “ ¬((FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre)) ”
  &&  emp
)

noncomputable def fits_return_wit_1_split_goal_1 : Prop :=
  forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : ((h1_pre + h2_pre) > b_pre)) (PreH2 : (h1_pre > b_pre)) (PreH3 : (h1_pre > h2_pre)) (PreH4 : ((w1_pre + w2_pre) <= a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  ¬((FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre))

noncomputable def fits_return_wit_2 : Prop :=
  (
forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : ((h1_pre + h2_pre) > b_pre)) (PreH2 : (h2_pre > b_pre)) (PreH3 : (h1_pre <= h2_pre)) (PreH4 : ((w1_pre + w2_pre) <= a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  TT && emp 
|--
  “ ((0 : Int) = (0 : Int)) ” &&
  “ ¬((FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre)) ”
  &&  emp
) \/
(
forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : ((h1_pre + h2_pre) > b_pre)) (PreH2 : (h2_pre > b_pre)) (PreH3 : (h1_pre <= h2_pre)) (PreH4 : ((w1_pre + w2_pre) <= a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  TT && emp 
|--
  “ ¬((FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre)) ”
  &&  emp
)

noncomputable def fits_return_wit_2_split_goal_1 : Prop :=
  forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : ((h1_pre + h2_pre) > b_pre)) (PreH2 : (h2_pre > b_pre)) (PreH3 : (h1_pre <= h2_pre)) (PreH4 : ((w1_pre + w2_pre) <= a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  ¬((FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre))

noncomputable def fits_return_wit_3 : Prop :=
  (
forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : ((h1_pre + h2_pre) > b_pre)) (PreH2 : ((w1_pre + w2_pre) > a_pre)) (PreH3 : (1 <= w1_pre)) (PreH4 : (w1_pre <= 100)) (PreH5 : (1 <= h1_pre)) (PreH6 : (h1_pre <= 100)) (PreH7 : (1 <= w2_pre)) (PreH8 : (w2_pre <= 100)) (PreH9 : (1 <= h2_pre)) (PreH10 : (h2_pre <= 100)) (PreH11 : (1 <= a_pre)) (PreH12 : (a_pre <= 100)) (PreH13 : (1 <= b_pre)) (PreH14 : (b_pre <= 100)) ,
  TT && emp 
|--
  “ ((0 : Int) = (0 : Int)) ” &&
  “ ¬((FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre)) ”
  &&  emp
) \/
(
forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : ((h1_pre + h2_pre) > b_pre)) (PreH2 : ((w1_pre + w2_pre) > a_pre)) (PreH3 : (1 <= w1_pre)) (PreH4 : (w1_pre <= 100)) (PreH5 : (1 <= h1_pre)) (PreH6 : (h1_pre <= 100)) (PreH7 : (1 <= w2_pre)) (PreH8 : (w2_pre <= 100)) (PreH9 : (1 <= h2_pre)) (PreH10 : (h2_pre <= 100)) (PreH11 : (1 <= a_pre)) (PreH12 : (a_pre <= 100)) (PreH13 : (1 <= b_pre)) (PreH14 : (b_pre <= 100)) ,
  TT && emp 
|--
  “ ¬((FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre)) ”
  &&  emp
)

noncomputable def fits_return_wit_3_split_goal_1 : Prop :=
  forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : ((h1_pre + h2_pre) > b_pre)) (PreH2 : ((w1_pre + w2_pre) > a_pre)) (PreH3 : (1 <= w1_pre)) (PreH4 : (w1_pre <= 100)) (PreH5 : (1 <= h1_pre)) (PreH6 : (h1_pre <= 100)) (PreH7 : (1 <= w2_pre)) (PreH8 : (w2_pre <= 100)) (PreH9 : (1 <= h2_pre)) (PreH10 : (h2_pre <= 100)) (PreH11 : (1 <= a_pre)) (PreH12 : (a_pre <= 100)) (PreH13 : (1 <= b_pre)) (PreH14 : (b_pre <= 100)) ,
  ¬((FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre))

noncomputable def fits_return_wit_4 : Prop :=
  (
forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (w2_pre > a_pre)) (PreH2 : (w1_pre <= w2_pre)) (PreH3 : ((h1_pre + h2_pre) <= b_pre)) (PreH4 : ((w1_pre + w2_pre) > a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  TT && emp 
|--
  “ ((0 : Int) = (0 : Int)) ” &&
  “ ¬((FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre)) ”
  &&  emp
) \/
(
forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (w2_pre > a_pre)) (PreH2 : (w1_pre <= w2_pre)) (PreH3 : ((h1_pre + h2_pre) <= b_pre)) (PreH4 : ((w1_pre + w2_pre) > a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  TT && emp 
|--
  “ ¬((FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre)) ”
  &&  emp
)

noncomputable def fits_return_wit_4_split_goal_1 : Prop :=
  forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (w2_pre > a_pre)) (PreH2 : (w1_pre <= w2_pre)) (PreH3 : ((h1_pre + h2_pre) <= b_pre)) (PreH4 : ((w1_pre + w2_pre) > a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  ¬((FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre))

noncomputable def fits_return_wit_5 : Prop :=
  (
forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (w1_pre > a_pre)) (PreH2 : (w1_pre > w2_pre)) (PreH3 : ((h1_pre + h2_pre) <= b_pre)) (PreH4 : ((w1_pre + w2_pre) > a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  TT && emp 
|--
  “ ((0 : Int) = (0 : Int)) ” &&
  “ ¬((FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre)) ”
  &&  emp
) \/
(
forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (w1_pre > a_pre)) (PreH2 : (w1_pre > w2_pre)) (PreH3 : ((h1_pre + h2_pre) <= b_pre)) (PreH4 : ((w1_pre + w2_pre) > a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  TT && emp 
|--
  “ ¬((FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre)) ”
  &&  emp
)

noncomputable def fits_return_wit_5_split_goal_1 : Prop :=
  forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (w1_pre > a_pre)) (PreH2 : (w1_pre > w2_pre)) (PreH3 : ((h1_pre + h2_pre) <= b_pre)) (PreH4 : ((w1_pre + w2_pre) > a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  ¬((FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre))

noncomputable def fits_return_wit_6 : Prop :=
  (
forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (w2_pre <= a_pre)) (PreH2 : (w1_pre <= w2_pre)) (PreH3 : ((h1_pre + h2_pre) <= b_pre)) (PreH4 : ((w1_pre + w2_pre) > a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  TT && emp 
|--
  “ (1 = 1) ” &&
  “ (FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre) ”
  &&  emp
) \/
(
forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (w2_pre <= a_pre)) (PreH2 : (w1_pre <= w2_pre)) (PreH3 : ((h1_pre + h2_pre) <= b_pre)) (PreH4 : ((w1_pre + w2_pre) > a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  TT && emp 
|--
  “ (FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre) ”
  &&  emp
)

noncomputable def fits_return_wit_6_split_goal_1 : Prop :=
  forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (w2_pre <= a_pre)) (PreH2 : (w1_pre <= w2_pre)) (PreH3 : ((h1_pre + h2_pre) <= b_pre)) (PreH4 : ((w1_pre + w2_pre) > a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  (FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre)

noncomputable def fits_return_wit_7 : Prop :=
  (
forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (w1_pre <= a_pre)) (PreH2 : (w1_pre > w2_pre)) (PreH3 : ((h1_pre + h2_pre) <= b_pre)) (PreH4 : ((w1_pre + w2_pre) > a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  TT && emp 
|--
  “ (1 = 1) ” &&
  “ (FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre) ”
  &&  emp
) \/
(
forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (w1_pre <= a_pre)) (PreH2 : (w1_pre > w2_pre)) (PreH3 : ((h1_pre + h2_pre) <= b_pre)) (PreH4 : ((w1_pre + w2_pre) > a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  TT && emp 
|--
  “ (FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre) ”
  &&  emp
)

noncomputable def fits_return_wit_7_split_goal_1 : Prop :=
  forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (w1_pre <= a_pre)) (PreH2 : (w1_pre > w2_pre)) (PreH3 : ((h1_pre + h2_pre) <= b_pre)) (PreH4 : ((w1_pre + w2_pre) > a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  (FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre)

noncomputable def fits_return_wit_8 : Prop :=
  (
forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (h2_pre <= b_pre)) (PreH2 : (h1_pre <= h2_pre)) (PreH3 : ((w1_pre + w2_pre) <= a_pre)) (PreH4 : (1 <= w1_pre)) (PreH5 : (w1_pre <= 100)) (PreH6 : (1 <= h1_pre)) (PreH7 : (h1_pre <= 100)) (PreH8 : (1 <= w2_pre)) (PreH9 : (w2_pre <= 100)) (PreH10 : (1 <= h2_pre)) (PreH11 : (h2_pre <= 100)) (PreH12 : (1 <= a_pre)) (PreH13 : (a_pre <= 100)) (PreH14 : (1 <= b_pre)) (PreH15 : (b_pre <= 100)) ,
  TT && emp 
|--
  “ (1 = 1) ” &&
  “ (FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre) ”
  &&  emp
) \/
(
forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (h2_pre <= b_pre)) (PreH2 : (h1_pre <= h2_pre)) (PreH3 : ((w1_pre + w2_pre) <= a_pre)) (PreH4 : (1 <= w1_pre)) (PreH5 : (w1_pre <= 100)) (PreH6 : (1 <= h1_pre)) (PreH7 : (h1_pre <= 100)) (PreH8 : (1 <= w2_pre)) (PreH9 : (w2_pre <= 100)) (PreH10 : (1 <= h2_pre)) (PreH11 : (h2_pre <= 100)) (PreH12 : (1 <= a_pre)) (PreH13 : (a_pre <= 100)) (PreH14 : (1 <= b_pre)) (PreH15 : (b_pre <= 100)) ,
  TT && emp 
|--
  “ (FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre) ”
  &&  emp
)

noncomputable def fits_return_wit_8_split_goal_1 : Prop :=
  forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (h2_pre <= b_pre)) (PreH2 : (h1_pre <= h2_pre)) (PreH3 : ((w1_pre + w2_pre) <= a_pre)) (PreH4 : (1 <= w1_pre)) (PreH5 : (w1_pre <= 100)) (PreH6 : (1 <= h1_pre)) (PreH7 : (h1_pre <= 100)) (PreH8 : (1 <= w2_pre)) (PreH9 : (w2_pre <= 100)) (PreH10 : (1 <= h2_pre)) (PreH11 : (h2_pre <= 100)) (PreH12 : (1 <= a_pre)) (PreH13 : (a_pre <= 100)) (PreH14 : (1 <= b_pre)) (PreH15 : (b_pre <= 100)) ,
  (FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre)

noncomputable def fits_return_wit_9 : Prop :=
  (
forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (h1_pre <= b_pre)) (PreH2 : (h1_pre > h2_pre)) (PreH3 : ((w1_pre + w2_pre) <= a_pre)) (PreH4 : (1 <= w1_pre)) (PreH5 : (w1_pre <= 100)) (PreH6 : (1 <= h1_pre)) (PreH7 : (h1_pre <= 100)) (PreH8 : (1 <= w2_pre)) (PreH9 : (w2_pre <= 100)) (PreH10 : (1 <= h2_pre)) (PreH11 : (h2_pre <= 100)) (PreH12 : (1 <= a_pre)) (PreH13 : (a_pre <= 100)) (PreH14 : (1 <= b_pre)) (PreH15 : (b_pre <= 100)) ,
  TT && emp 
|--
  “ (1 = 1) ” &&
  “ (FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre) ”
  &&  emp
) \/
(
forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (h1_pre <= b_pre)) (PreH2 : (h1_pre > h2_pre)) (PreH3 : ((w1_pre + w2_pre) <= a_pre)) (PreH4 : (1 <= w1_pre)) (PreH5 : (w1_pre <= 100)) (PreH6 : (1 <= h1_pre)) (PreH7 : (h1_pre <= 100)) (PreH8 : (1 <= w2_pre)) (PreH9 : (w2_pre <= 100)) (PreH10 : (1 <= h2_pre)) (PreH11 : (h2_pre <= 100)) (PreH12 : (1 <= a_pre)) (PreH13 : (a_pre <= 100)) (PreH14 : (1 <= b_pre)) (PreH15 : (b_pre <= 100)) ,
  TT && emp 
|--
  “ (FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre) ”
  &&  emp
)

noncomputable def fits_return_wit_9_split_goal_1 : Prop :=
  forall (w1_pre : Int) (h1_pre : Int) (w2_pre : Int) (h2_pre : Int) (a_pre : Int) (b_pre : Int) (PreH1 : (h1_pre <= b_pre)) (PreH2 : (h1_pre > h2_pre)) (PreH3 : ((w1_pre + w2_pre) <= a_pre)) (PreH4 : (1 <= w1_pre)) (PreH5 : (w1_pre <= 100)) (PreH6 : (1 <= h1_pre)) (PreH7 : (h1_pre <= 100)) (PreH8 : (1 <= w2_pre)) (PreH9 : (w2_pre <= 100)) (PreH10 : (1 <= h2_pre)) (PreH11 : (h2_pre <= 100)) (PreH12 : (1 <= a_pre)) (PreH13 : (a_pre <= 100)) (PreH14 : (1 <= b_pre)) (PreH15 : (b_pre <= 100)) ,
  (FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre)

noncomputable def solver_safety_wit_1 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (xs_spec : (List Int)) (ys_spec : (List Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (1 <= (fst (paper)))) (PreH2 : ((fst (paper)) <= 100)) (PreH3 : (1 <= (snd (paper)))) (PreH4 : ((snd (paper)) <= 100)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((1 <= (fst ((Znth i seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth i seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth i seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth i seals __default__Prod_Z_Z))) <= 100)))) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec)) = n_pre)) (PreH12 : ((Zlength (ys_spec)) = n_pre)) (PreH13 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((Znth i_2 xs_spec (0 : Int)) = (fst ((Znth i_2 seals __default__Prod_Z_Z)))) ∧ ((Znth i_2 ys_spec (0 : Int)) = (snd ((Znth i_2 seals __default__Prod_Z_Z))))))) ,
  ((( &( "best" ) )) # Int |->_)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (xs_spec : (List Int)) (ys_spec : (List Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (1 <= (fst (paper)))) (PreH2 : ((fst (paper)) <= 100)) (PreH3 : (1 <= (snd (paper)))) (PreH4 : ((snd (paper)) <= 100)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((1 <= (fst ((Znth i seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth i seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth i seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth i seals __default__Prod_Z_Z))) <= 100)))) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec)) = n_pre)) (PreH12 : ((Zlength (ys_spec)) = n_pre)) (PreH13 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((Znth i_2 xs_spec (0 : Int)) = (fst ((Znth i_2 seals __default__Prod_Z_Z)))) ∧ ((Znth i_2 ys_spec (0 : Int)) = (snd ((Znth i_2 seals __default__Prod_Z_Z))))))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec)) = n_pre)) (PreH12 : ((Zlength (ys_spec)) = n_pre)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= best)) (PreH17 : (best <= 20000)) (PreH18 : (BestBefore paper seals i (i + 1) (0 : Int) (0 : Int) best)) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec)) = n_pre)) (PreH12 : ((Zlength (ys_spec)) = n_pre)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= best)) (PreH17 : (best <= 20000)) (PreH18 : (BestBefore paper seals i (i + 1) (0 : Int) (0 : Int) best)) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (j < n_pre)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec)) = n_pre)) (PreH12 : ((Zlength (ys_spec)) = n_pre)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((i + 1) <= j)) (PreH17 : (j <= n_pre)) (PreH18 : ((0 : Int) <= best)) (PreH19 : (best <= 20000)) (PreH20 : (BestBefore paper seals i j (0 : Int) (0 : Int) best)) ,
  ((( &( "ri" ) )) # Int |->_)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (1 <= (fst (paper)))) (PreH2 : ((fst (paper)) <= 100)) (PreH3 : (1 <= (snd (paper)))) (PreH4 : ((snd (paper)) <= 100)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : ((fst (paper)) = a_pre)) (PreH8 : ((snd (paper)) = b_pre)) (PreH9 : (n_pre = (Zlength (seals)))) (PreH10 : ((Zlength (xs_spec)) = n_pre)) (PreH11 : ((Zlength (ys_spec)) = n_pre)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < j)) (PreH15 : (j < n_pre)) (PreH16 : ((0 : Int) <= ri)) (PreH17 : (ri <= 2)) (PreH18 : ((0 : Int) <= best)) (PreH19 : (best <= 20000)) (PreH20 : (BestBefore paper seals i j ri (0 : Int) best)) ,
  ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_7 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (ri < 2)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec)) = n_pre)) (PreH12 : ((Zlength (ys_spec)) = n_pre)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < j)) (PreH16 : (j < n_pre)) (PreH17 : ((0 : Int) <= ri)) (PreH18 : (ri <= 2)) (PreH19 : ((0 : Int) <= best)) (PreH20 : (best <= 20000)) (PreH21 : (BestBefore paper seals i j ri (0 : Int) best)) ,
  ((( &( "rj" ) )) # Int |->_)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_8 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (1 <= (fst (paper)))) (PreH2 : ((fst (paper)) <= 100)) (PreH3 : (1 <= (snd (paper)))) (PreH4 : ((snd (paper)) <= 100)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : ((fst (paper)) = a_pre)) (PreH8 : ((snd (paper)) = b_pre)) (PreH9 : (n_pre = (Zlength (seals)))) (PreH10 : ((Zlength (xs_spec)) = n_pre)) (PreH11 : ((Zlength (ys_spec)) = n_pre)) (PreH12 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < j)) (PreH15 : (j < n_pre)) (PreH16 : ((0 : Int) <= ri)) (PreH17 : (ri < 2)) (PreH18 : ((0 : Int) <= rj)) (PreH19 : (rj <= 2)) (PreH20 : ((0 : Int) <= best)) (PreH21 : (best <= 20000)) (PreH22 : (BestBefore paper seals i j ri rj best)) ,
  ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_9 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (ri = (0 : Int))) (PreH2 : (ri ≠ (0 : Int))) (PreH3 : (rj < 2)) (PreH4 : (1 <= (fst (paper)))) (PreH5 : ((fst (paper)) <= 100)) (PreH6 : (1 <= (snd (paper)))) (PreH7 : ((snd (paper)) <= 100)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((fst (paper)) = a_pre)) (PreH11 : ((snd (paper)) = b_pre)) (PreH12 : (n_pre = (Zlength (seals)))) (PreH13 : ((Zlength (xs_spec)) = n_pre)) (PreH14 : ((Zlength (ys_spec)) = n_pre)) (PreH15 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < j)) (PreH18 : (j < n_pre)) (PreH19 : ((0 : Int) <= ri)) (PreH20 : (ri < 2)) (PreH21 : ((0 : Int) <= rj)) (PreH22 : (rj <= 2)) (PreH23 : ((0 : Int) <= best)) (PreH24 : (best <= 20000)) (PreH25 : (BestBefore paper seals i j ri rj best)) ,
  ((( &( "h1" ) )) # Int |->_)
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full x_pre n_pre xs_spec)
|--
  “ False ”

noncomputable def solver_safety_wit_10 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (ri ≠ (0 : Int))) (PreH2 : (ri = (0 : Int))) (PreH3 : (rj < 2)) (PreH4 : (1 <= (fst (paper)))) (PreH5 : ((fst (paper)) <= 100)) (PreH6 : (1 <= (snd (paper)))) (PreH7 : ((snd (paper)) <= 100)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((fst (paper)) = a_pre)) (PreH11 : ((snd (paper)) = b_pre)) (PreH12 : (n_pre = (Zlength (seals)))) (PreH13 : ((Zlength (xs_spec)) = n_pre)) (PreH14 : ((Zlength (ys_spec)) = n_pre)) (PreH15 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < j)) (PreH18 : (j < n_pre)) (PreH19 : ((0 : Int) <= ri)) (PreH20 : (ri < 2)) (PreH21 : ((0 : Int) <= rj)) (PreH22 : (rj <= 2)) (PreH23 : ((0 : Int) <= best)) (PreH24 : (best <= 20000)) (PreH25 : (BestBefore paper seals i j ri rj best)) ,
  ((( &( "h1" ) )) # Int |->_)
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full y_pre n_pre ys_spec)
|--
  “ False ”

noncomputable def solver_safety_wit_11 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (rj = (0 : Int))) (PreH2 : (rj ≠ (0 : Int))) (PreH3 : (ri ≠ (0 : Int))) (PreH4 : (ri ≠ (0 : Int))) (PreH5 : (rj < 2)) (PreH6 : (1 <= (fst (paper)))) (PreH7 : ((fst (paper)) <= 100)) (PreH8 : (1 <= (snd (paper)))) (PreH9 : ((snd (paper)) <= 100)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : ((fst (paper)) = a_pre)) (PreH13 : ((snd (paper)) = b_pre)) (PreH14 : (n_pre = (Zlength (seals)))) (PreH15 : ((Zlength (xs_spec)) = n_pre)) (PreH16 : ((Zlength (ys_spec)) = n_pre)) (PreH17 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i < j)) (PreH20 : (j < n_pre)) (PreH21 : ((0 : Int) <= ri)) (PreH22 : (ri < 2)) (PreH23 : ((0 : Int) <= rj)) (PreH24 : (rj <= 2)) (PreH25 : ((0 : Int) <= best)) (PreH26 : (best <= 20000)) (PreH27 : (BestBefore paper seals i j ri rj best)) ,
  ((( &( "h2" ) )) # Int |->_)
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ False ”

noncomputable def solver_safety_wit_12 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (rj ≠ (0 : Int))) (PreH2 : (rj = (0 : Int))) (PreH3 : (ri ≠ (0 : Int))) (PreH4 : (ri ≠ (0 : Int))) (PreH5 : (rj < 2)) (PreH6 : (1 <= (fst (paper)))) (PreH7 : ((fst (paper)) <= 100)) (PreH8 : (1 <= (snd (paper)))) (PreH9 : ((snd (paper)) <= 100)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : ((fst (paper)) = a_pre)) (PreH13 : ((snd (paper)) = b_pre)) (PreH14 : (n_pre = (Zlength (seals)))) (PreH15 : ((Zlength (xs_spec)) = n_pre)) (PreH16 : ((Zlength (ys_spec)) = n_pre)) (PreH17 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i < j)) (PreH20 : (j < n_pre)) (PreH21 : ((0 : Int) <= ri)) (PreH22 : (ri < 2)) (PreH23 : ((0 : Int) <= rj)) (PreH24 : (rj <= 2)) (PreH25 : ((0 : Int) <= best)) (PreH26 : (best <= 20000)) (PreH27 : (BestBefore paper seals i j ri rj best)) ,
  ((( &( "h2" ) )) # Int |->_)
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ False ”

noncomputable def solver_safety_wit_13 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (rj = (0 : Int))) (PreH2 : (rj ≠ (0 : Int))) (PreH3 : (ri = (0 : Int))) (PreH4 : (ri = (0 : Int))) (PreH5 : (rj < 2)) (PreH6 : (1 <= (fst (paper)))) (PreH7 : ((fst (paper)) <= 100)) (PreH8 : (1 <= (snd (paper)))) (PreH9 : ((snd (paper)) <= 100)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : ((fst (paper)) = a_pre)) (PreH13 : ((snd (paper)) = b_pre)) (PreH14 : (n_pre = (Zlength (seals)))) (PreH15 : ((Zlength (xs_spec)) = n_pre)) (PreH16 : ((Zlength (ys_spec)) = n_pre)) (PreH17 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i < j)) (PreH20 : (j < n_pre)) (PreH21 : ((0 : Int) <= ri)) (PreH22 : (ri < 2)) (PreH23 : ((0 : Int) <= rj)) (PreH24 : (rj <= 2)) (PreH25 : ((0 : Int) <= best)) (PreH26 : (best <= 20000)) (PreH27 : (BestBefore paper seals i j ri rj best)) ,
  ((( &( "h2" ) )) # Int |->_)
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ False ”

noncomputable def solver_safety_wit_14 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (rj ≠ (0 : Int))) (PreH2 : (rj = (0 : Int))) (PreH3 : (ri = (0 : Int))) (PreH4 : (ri = (0 : Int))) (PreH5 : (rj < 2)) (PreH6 : (1 <= (fst (paper)))) (PreH7 : ((fst (paper)) <= 100)) (PreH8 : (1 <= (snd (paper)))) (PreH9 : ((snd (paper)) <= 100)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : ((fst (paper)) = a_pre)) (PreH13 : ((snd (paper)) = b_pre)) (PreH14 : (n_pre = (Zlength (seals)))) (PreH15 : ((Zlength (xs_spec)) = n_pre)) (PreH16 : ((Zlength (ys_spec)) = n_pre)) (PreH17 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i < j)) (PreH20 : (j < n_pre)) (PreH21 : ((0 : Int) <= ri)) (PreH22 : (ri < 2)) (PreH23 : ((0 : Int) <= rj)) (PreH24 : (rj <= 2)) (PreH25 : ((0 : Int) <= best)) (PreH26 : (best <= 20000)) (PreH27 : (BestBefore paper seals i j ri rj best)) ,
  ((( &( "h2" ) )) # Int |->_)
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ False ”

noncomputable def solver_safety_wit_15 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval = (0 : Int))) ,
  (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ False ”

noncomputable def solver_safety_wit_16 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval = (0 : Int))) ,
  (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ False ”

noncomputable def solver_safety_wit_17 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval = (0 : Int))) ,
  (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ False ”

noncomputable def solver_safety_wit_18 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval = (0 : Int))) ,
  (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ False ”

noncomputable def solver_safety_wit_19 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = (0 : Int))) (PreH2 : ¬((FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre))) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ False ”

noncomputable def solver_safety_wit_20 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = (0 : Int))) (PreH2 : ¬((FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre))) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ False ”

noncomputable def solver_safety_wit_21 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = (0 : Int))) (PreH2 : ¬((FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre))) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ False ”

noncomputable def solver_safety_wit_22 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = (0 : Int))) (PreH2 : ¬((FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre))) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ False ”

noncomputable def solver_safety_wit_23 : Prop :=
  (
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ ((((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int))) + ((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int)))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int))) + ((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int))))) ”
) \/
(
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ ((((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int))) + ((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int)))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int))) + ((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int))))) ”
)

noncomputable def solver_safety_wit_23_split_goal_1 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ ((((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int))) + ((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int)))) <= INT_MAX) ”

noncomputable def solver_safety_wit_23_split_goal_2 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ ((INT_MIN) <= (((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int))) + ((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int))))) ”

noncomputable def solver_safety_wit_24 : Prop :=
  (
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ (((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int)))) ”
) \/
(
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ (((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int)))) ”
)

noncomputable def solver_safety_wit_24_split_goal_1 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ (((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int))) <= INT_MAX) ”

noncomputable def solver_safety_wit_24_split_goal_2 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ ((INT_MIN) <= ((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int)))) ”

noncomputable def solver_safety_wit_25 : Prop :=
  (
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ (((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int)))) ”
) \/
(
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ (((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int)))) ”
)

noncomputable def solver_safety_wit_25_split_goal_1 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ (((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int))) <= INT_MAX) ”

noncomputable def solver_safety_wit_25_split_goal_2 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ ((INT_MIN) <= ((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int)))) ”

noncomputable def solver_safety_wit_26 : Prop :=
  (
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ ((((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int))) + ((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int)))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int))) + ((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int))))) ”
) \/
(
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ ((((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int))) + ((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int)))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int))) + ((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int))))) ”
)

noncomputable def solver_safety_wit_26_split_goal_1 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ ((((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int))) + ((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int)))) <= INT_MAX) ”

noncomputable def solver_safety_wit_26_split_goal_2 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ ((INT_MIN) <= (((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int))) + ((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int))))) ”

noncomputable def solver_safety_wit_27 : Prop :=
  (
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ (((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int)))) ”
) \/
(
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ (((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int)))) ”
)

noncomputable def solver_safety_wit_27_split_goal_1 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ (((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int))) <= INT_MAX) ”

noncomputable def solver_safety_wit_27_split_goal_2 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ ((INT_MIN) <= ((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int)))) ”

noncomputable def solver_safety_wit_28 : Prop :=
  (
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ (((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int)))) ”
) \/
(
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ (((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int)))) ”
)

noncomputable def solver_safety_wit_28_split_goal_1 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ (((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int))) <= INT_MAX) ”

noncomputable def solver_safety_wit_28_split_goal_2 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ ((INT_MIN) <= ((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int)))) ”

noncomputable def solver_safety_wit_29 : Prop :=
  (
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ ((((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int))) + ((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int)))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int))) + ((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int))))) ”
) \/
(
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ ((((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int))) + ((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int)))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int))) + ((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int))))) ”
)

noncomputable def solver_safety_wit_29_split_goal_1 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ ((((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int))) + ((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int)))) <= INT_MAX) ”

noncomputable def solver_safety_wit_29_split_goal_2 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ ((INT_MIN) <= (((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int))) + ((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int))))) ”

noncomputable def solver_safety_wit_30 : Prop :=
  (
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ (((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int)))) ”
) \/
(
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ (((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int)))) ”
)

noncomputable def solver_safety_wit_30_split_goal_1 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ (((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int))) <= INT_MAX) ”

noncomputable def solver_safety_wit_30_split_goal_2 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ ((INT_MIN) <= ((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int)))) ”

noncomputable def solver_safety_wit_31 : Prop :=
  (
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ (((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int)))) ”
) \/
(
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ (((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int)))) ”
)

noncomputable def solver_safety_wit_31_split_goal_1 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ (((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int))) <= INT_MAX) ”

noncomputable def solver_safety_wit_31_split_goal_2 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ ((INT_MIN) <= ((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int)))) ”

noncomputable def solver_safety_wit_32 : Prop :=
  (
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ ((((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int))) + ((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int)))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int))) + ((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int))))) ”
) \/
(
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ ((((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int))) + ((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int)))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int))) + ((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int))))) ”
)

noncomputable def solver_safety_wit_32_split_goal_1 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ ((((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int))) + ((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int)))) <= INT_MAX) ”

noncomputable def solver_safety_wit_32_split_goal_2 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ ((INT_MIN) <= (((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int))) + ((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int))))) ”

noncomputable def solver_safety_wit_33 : Prop :=
  (
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ (((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int)))) ”
) \/
(
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ (((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int)))) ”
)

noncomputable def solver_safety_wit_33_split_goal_1 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ (((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int))) <= INT_MAX) ”

noncomputable def solver_safety_wit_33_split_goal_2 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ ((INT_MIN) <= ((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int)))) ”

noncomputable def solver_safety_wit_34 : Prop :=
  (
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ (((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int)))) ”
) \/
(
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ (((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int)))) ”
)

noncomputable def solver_safety_wit_34_split_goal_1 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ (((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int))) <= INT_MAX) ”

noncomputable def solver_safety_wit_34_split_goal_2 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  ((( &( "area" ) )) # Int |->_)
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ ((INT_MIN) <= ((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int)))) ”

noncomputable def solver_safety_wit_35 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (j >= n_pre)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec)) = n_pre)) (PreH12 : ((Zlength (ys_spec)) = n_pre)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((i + 1) <= j)) (PreH17 : (j <= n_pre)) (PreH18 : ((0 : Int) <= best)) (PreH19 : (best <= 20000)) (PreH20 : (BestBefore paper seals i j (0 : Int) (0 : Int) best)) ,
  ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_36 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (ri >= 2)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec)) = n_pre)) (PreH12 : ((Zlength (ys_spec)) = n_pre)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < j)) (PreH16 : (j < n_pre)) (PreH17 : ((0 : Int) <= ri)) (PreH18 : (ri <= 2)) (PreH19 : ((0 : Int) <= best)) (PreH20 : (best <= 20000)) (PreH21 : (BestBefore paper seals i j ri (0 : Int) best)) ,
  ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def solver_safety_wit_37 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (rj >= 2)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec)) = n_pre)) (PreH12 : ((Zlength (ys_spec)) = n_pre)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < j)) (PreH16 : (j < n_pre)) (PreH17 : ((0 : Int) <= ri)) (PreH18 : (ri < 2)) (PreH19 : ((0 : Int) <= rj)) (PreH20 : (rj <= 2)) (PreH21 : ((0 : Int) <= best)) (PreH22 : (best <= 20000)) (PreH23 : (BestBefore paper seals i j ri rj best)) ,
  ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
|--
  “ ((ri + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (ri + 1)) ”

noncomputable def solver_safety_wit_38 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : ((((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int))) + ((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int)))) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (rj ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (ri ≠ (0 : Int))) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec)) = n_pre)) (PreH19 : ((Zlength (ys_spec)) = n_pre)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : ((0 : Int) <= ri)) (PreH25 : (ri < 2)) (PreH26 : ((0 : Int) <= rj)) (PreH27 : (rj <= 2)) (PreH28 : ((0 : Int) <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best)) (PreH31 : (retval ≠ (0 : Int))) ,
  (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> ((((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int))) + ((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int))))))
|--
  “ ((rj + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (rj + 1)) ”

noncomputable def solver_safety_wit_39 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : ((((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int))) + ((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int)))) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) (PreH4 : (rj = (0 : Int))) (PreH5 : (rj = (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (ri ≠ (0 : Int))) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec)) = n_pre)) (PreH19 : ((Zlength (ys_spec)) = n_pre)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : ((0 : Int) <= ri)) (PreH25 : (ri < 2)) (PreH26 : ((0 : Int) <= rj)) (PreH27 : (rj <= 2)) (PreH28 : ((0 : Int) <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best)) (PreH31 : (retval ≠ (0 : Int))) ,
  (intArray.full y_pre n_pre ys_spec)
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> ((((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int))) + ((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int))))))
|--
  “ ((rj + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (rj + 1)) ”

noncomputable def solver_safety_wit_40 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : ((((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int))) + ((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int)))) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (rj ≠ (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (ri = (0 : Int))) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec)) = n_pre)) (PreH19 : ((Zlength (ys_spec)) = n_pre)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : ((0 : Int) <= ri)) (PreH25 : (ri < 2)) (PreH26 : ((0 : Int) <= rj)) (PreH27 : (rj <= 2)) (PreH28 : ((0 : Int) <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best)) (PreH31 : (retval ≠ (0 : Int))) ,
  (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> ((((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int))) + ((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int))))))
|--
  “ ((rj + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (rj + 1)) ”

noncomputable def solver_safety_wit_41 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : ((((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int))) + ((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int)))) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) (PreH4 : (rj = (0 : Int))) (PreH5 : (rj = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (ri = (0 : Int))) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec)) = n_pre)) (PreH19 : ((Zlength (ys_spec)) = n_pre)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : ((0 : Int) <= ri)) (PreH25 : (ri < 2)) (PreH26 : ((0 : Int) <= rj)) (PreH27 : (rj <= 2)) (PreH28 : ((0 : Int) <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best)) (PreH31 : (retval ≠ (0 : Int))) ,
  (intArray.full y_pre n_pre ys_spec)
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> ((((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int))) + ((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int))))))
|--
  “ ((rj + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (rj + 1)) ”

noncomputable def solver_safety_wit_42 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : ((((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int))) + ((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int)))) <= best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (rj ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (ri ≠ (0 : Int))) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec)) = n_pre)) (PreH19 : ((Zlength (ys_spec)) = n_pre)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : ((0 : Int) <= ri)) (PreH25 : (ri < 2)) (PreH26 : ((0 : Int) <= rj)) (PreH27 : (rj <= 2)) (PreH28 : ((0 : Int) <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best)) (PreH31 : (retval ≠ (0 : Int))) ,
  (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ ((rj + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (rj + 1)) ”

noncomputable def solver_safety_wit_43 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : ((((Znth i ys_spec (0 : Int)) * (Znth i xs_spec (0 : Int))) + ((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int)))) <= best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) (PreH4 : (rj = (0 : Int))) (PreH5 : (rj = (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (ri ≠ (0 : Int))) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec)) = n_pre)) (PreH19 : ((Zlength (ys_spec)) = n_pre)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : ((0 : Int) <= ri)) (PreH25 : (ri < 2)) (PreH26 : ((0 : Int) <= rj)) (PreH27 : (rj <= 2)) (PreH28 : ((0 : Int) <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best)) (PreH31 : (retval ≠ (0 : Int))) ,
  (intArray.full y_pre n_pre ys_spec)
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ ((rj + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (rj + 1)) ”

noncomputable def solver_safety_wit_44 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : ((((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int))) + ((Znth j ys_spec (0 : Int)) * (Znth j xs_spec (0 : Int)))) <= best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (rj ≠ (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (ri = (0 : Int))) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec)) = n_pre)) (PreH19 : ((Zlength (ys_spec)) = n_pre)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : ((0 : Int) <= ri)) (PreH25 : (ri < 2)) (PreH26 : ((0 : Int) <= rj)) (PreH27 : (rj <= 2)) (PreH28 : ((0 : Int) <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best)) (PreH31 : (retval ≠ (0 : Int))) ,
  (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ ((rj + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (rj + 1)) ”

noncomputable def solver_safety_wit_45 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : ((((Znth i xs_spec (0 : Int)) * (Znth i ys_spec (0 : Int))) + ((Znth j xs_spec (0 : Int)) * (Znth j ys_spec (0 : Int)))) <= best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) (PreH4 : (rj = (0 : Int))) (PreH5 : (rj = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (ri = (0 : Int))) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec)) = n_pre)) (PreH19 : ((Zlength (ys_spec)) = n_pre)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : ((0 : Int) <= ri)) (PreH25 : (ri < 2)) (PreH26 : ((0 : Int) <= rj)) (PreH27 : (rj <= 2)) (PreH28 : ((0 : Int) <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best)) (PreH31 : (retval ≠ (0 : Int))) ,
  (intArray.full y_pre n_pre ys_spec)
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ ((rj + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (rj + 1)) ”

noncomputable def solver_safety_wit_46 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = (0 : Int))) (PreH2 : ¬((FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre))) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval = (0 : Int))) ,
  (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ ((rj + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (rj + 1)) ”

noncomputable def solver_safety_wit_47 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = (0 : Int))) (PreH2 : ¬((FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre))) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval = (0 : Int))) ,
  (intArray.full y_pre n_pre ys_spec)
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ ((rj + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (rj + 1)) ”

noncomputable def solver_safety_wit_48 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = (0 : Int))) (PreH2 : ¬((FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre))) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval = (0 : Int))) ,
  (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ ((rj + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (rj + 1)) ”

noncomputable def solver_safety_wit_49 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = (0 : Int))) (PreH2 : ¬((FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre))) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval = (0 : Int))) ,
  (intArray.full y_pre n_pre ys_spec)
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ ((rj + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (rj + 1)) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (xs_spec_2 : (List Int)) (ys_spec_2 : (List Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (1 <= (fst (paper)))) (PreH2 : ((fst (paper)) <= 100)) (PreH3 : (1 <= (snd (paper)))) (PreH4 : ((snd (paper)) <= 100)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((1 <= (fst ((Znth i seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth i seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth i seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth i seals __default__Prod_Z_Z))) <= 100)))) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((Znth i_2 xs_spec_2 (0 : Int)) = (fst ((Znth i_2 seals __default__Prod_Z_Z)))) ∧ ((Znth i_2 ys_spec_2 (0 : Int)) = (snd ((Znth i_2 seals __default__Prod_Z_Z))))))) ,
  (intArray.full x_pre n_pre xs_spec_2)
  ** (intArray.full y_pre n_pre ys_spec_2)
|--
  EX ys_spec : (List Int), EX xs_spec : (List Int),
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 20000) ” &&
  “ (BestBefore paper seals (0 : Int) ((0 : Int) + 1) (0 : Int) (0 : Int) (0 : Int)) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
) \/
(
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (xs_spec_2 : (List Int)) (ys_spec_2 : (List Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (1 <= (fst (paper)))) (PreH2 : ((fst (paper)) <= 100)) (PreH3 : (1 <= (snd (paper)))) (PreH4 : ((snd (paper)) <= 100)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((1 <= (fst ((Znth i seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth i seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth i seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth i seals __default__Prod_Z_Z))) <= 100)))) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((Znth i_2 xs_spec_2 (0 : Int)) = (fst ((Znth i_2 seals __default__Prod_Z_Z)))) ∧ ((Znth i_2 ys_spec_2 (0 : Int)) = (snd ((Znth i_2 seals __default__Prod_Z_Z))))))) ,
  TT && emp 
|--
  “ (BestBefore paper seals (0 : Int) ((0 : Int) + 1) (0 : Int) (0 : Int) (0 : Int)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ”
  &&  emp
)

noncomputable def solver_entail_wit_1_split_goal_1 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (xs_spec_2 : (List Int)) (ys_spec_2 : (List Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (1 <= (fst (paper)))) (PreH2 : ((fst (paper)) <= 100)) (PreH3 : (1 <= (snd (paper)))) (PreH4 : ((snd (paper)) <= 100)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((1 <= (fst ((Znth i seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth i seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth i seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth i seals __default__Prod_Z_Z))) <= 100)))) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((Znth i_2 xs_spec_2 (0 : Int)) = (fst ((Znth i_2 seals __default__Prod_Z_Z)))) ∧ ((Znth i_2 ys_spec_2 (0 : Int)) = (snd ((Znth i_2 seals __default__Prod_Z_Z))))))) ,
  (BestBefore paper seals (0 : Int) ((0 : Int) + 1) (0 : Int) (0 : Int) (0 : Int))

noncomputable def solver_entail_wit_1_split_goal_2 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (xs_spec_2 : (List Int)) (ys_spec_2 : (List Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (1 <= (fst (paper)))) (PreH2 : ((fst (paper)) <= 100)) (PreH3 : (1 <= (snd (paper)))) (PreH4 : ((snd (paper)) <= 100)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((1 <= (fst ((Znth i seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth i seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth i seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth i seals __default__Prod_Z_Z))) <= 100)))) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < n_pre)) -> (((Znth i_2 xs_spec_2 (0 : Int)) = (fst ((Znth i_2 seals __default__Prod_Z_Z)))) ∧ ((Znth i_2 ys_spec_2 (0 : Int)) = (snd ((Znth i_2 seals __default__Prod_Z_Z))))))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))

noncomputable def solver_entail_wit_2 : Prop :=
  (
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k_2 xs_spec_2 (0 : Int)) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((Znth k_2 ys_spec_2 (0 : Int)) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= best)) (PreH17 : (best <= 20000)) (PreH18 : (BestBefore paper seals i (i + 1) (0 : Int) (0 : Int) best)) ,
  (intArray.full x_pre n_pre xs_spec_2)
  ** (intArray.full y_pre n_pre ys_spec_2)
|--
  EX ys_spec : (List Int), EX xs_spec : (List Int),
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((i + 1) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i (i + 1) (0 : Int) (0 : Int) best) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
) \/
(
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k_2 xs_spec_2 (0 : Int)) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((Znth k_2 ys_spec_2 (0 : Int)) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= best)) (PreH17 : (best <= 20000)) (PreH18 : (BestBefore paper seals i (i + 1) (0 : Int) (0 : Int) best)) ,
  TT && emp 
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_split_goal_1 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k_2 xs_spec_2 (0 : Int)) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((Znth k_2 ys_spec_2 (0 : Int)) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= best)) (PreH17 : (best <= 20000)) (PreH18 : (BestBefore paper seals i (i + 1) (0 : Int) (0 : Int) best)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))

noncomputable def solver_entail_wit_3 : Prop :=
  (
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (j < n_pre)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k_2 xs_spec_2 (0 : Int)) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((Znth k_2 ys_spec_2 (0 : Int)) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((i + 1) <= j)) (PreH17 : (j <= n_pre)) (PreH18 : ((0 : Int) <= best)) (PreH19 : (best <= 20000)) (PreH20 : (BestBefore paper seals i j (0 : Int) (0 : Int) best)) ,
  (intArray.full x_pre n_pre xs_spec_2)
  ** (intArray.full y_pre n_pre ys_spec_2)
|--
  EX ys_spec : (List Int), EX xs_spec : (List Int),
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j (0 : Int) (0 : Int) best) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
) \/
(
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (j < n_pre)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k_2 xs_spec_2 (0 : Int)) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((Znth k_2 ys_spec_2 (0 : Int)) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((i + 1) <= j)) (PreH17 : (j <= n_pre)) (PreH18 : ((0 : Int) <= best)) (PreH19 : (best <= 20000)) (PreH20 : (BestBefore paper seals i j (0 : Int) (0 : Int) best)) ,
  TT && emp 
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ”
  &&  emp
)

noncomputable def solver_entail_wit_3_split_goal_1 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (j < n_pre)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k_2 xs_spec_2 (0 : Int)) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((Znth k_2 ys_spec_2 (0 : Int)) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((i + 1) <= j)) (PreH17 : (j <= n_pre)) (PreH18 : ((0 : Int) <= best)) (PreH19 : (best <= 20000)) (PreH20 : (BestBefore paper seals i j (0 : Int) (0 : Int) best)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))

noncomputable def solver_entail_wit_4 : Prop :=
  (
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (ri < 2)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k_2 xs_spec_2 (0 : Int)) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((Znth k_2 ys_spec_2 (0 : Int)) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < j)) (PreH16 : (j < n_pre)) (PreH17 : ((0 : Int) <= ri)) (PreH18 : (ri <= 2)) (PreH19 : ((0 : Int) <= best)) (PreH20 : (best <= 20000)) (PreH21 : (BestBefore paper seals i j ri (0 : Int) best)) ,
  (intArray.full x_pre n_pre xs_spec_2)
  ** (intArray.full y_pre n_pre ys_spec_2)
|--
  EX ys_spec : (List Int), EX xs_spec : (List Int),
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri (0 : Int) best) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
) \/
(
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (ri < 2)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k_2 xs_spec_2 (0 : Int)) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((Znth k_2 ys_spec_2 (0 : Int)) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < j)) (PreH16 : (j < n_pre)) (PreH17 : ((0 : Int) <= ri)) (PreH18 : (ri <= 2)) (PreH19 : ((0 : Int) <= best)) (PreH20 : (best <= 20000)) (PreH21 : (BestBefore paper seals i j ri (0 : Int) best)) ,
  TT && emp 
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ”
  &&  emp
)

noncomputable def solver_entail_wit_4_split_goal_1 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (ri < 2)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k_2 xs_spec_2 (0 : Int)) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((Znth k_2 ys_spec_2 (0 : Int)) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < j)) (PreH16 : (j < n_pre)) (PreH17 : ((0 : Int) <= ri)) (PreH18 : (ri <= 2)) (PreH19 : ((0 : Int) <= best)) (PreH20 : (best <= 20000)) (PreH21 : (BestBefore paper seals i j ri (0 : Int) best)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))

noncomputable def solver_entail_wit_5_1 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = (0 : Int))) (PreH2 : ¬((FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre))) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval = (0 : Int))) ,
  (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
|--
  “ (retval = (0 : Int)) ” &&
  “ ¬((FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval = (0 : Int)) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))

noncomputable def solver_entail_wit_5_2 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval_5 : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval_5 = 1)) (PreH2 : (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval_5 = (0 : Int))) ,
  (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
|--
  (EX retval : Int,
  “ (retval = (0 : Int)) ” &&
  “ ¬((FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval = (0 : Int)) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int)))))
  ||
  (EX retval_2 : Int,
  “ (retval_2 = (0 : Int)) ” &&
  “ ¬((FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval_2 = (0 : Int)) ”
  &&  (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int)))))
  ||
  (EX retval_3 : Int,
  “ (retval_3 = (0 : Int)) ” &&
  “ ¬((FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval_3 = (0 : Int)) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int)))))
  ||
  (EX retval_4 : Int,
  “ (retval_4 = (0 : Int)) ” &&
  “ ¬((FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval_4 = (0 : Int)) ”
  &&  (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int)))))

noncomputable def solver_entail_wit_5_3 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval_2 : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval_2 = (0 : Int))) (PreH2 : ¬((FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre))) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval_2 = (0 : Int))) ,
  (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
|--
  “ (retval_2 = (0 : Int)) ” &&
  “ ¬((FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval_2 = (0 : Int)) ”
  &&  (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))

noncomputable def solver_entail_wit_5_4 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval_5 : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval_5 = 1)) (PreH2 : (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval_5 = (0 : Int))) ,
  (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
|--
  (EX retval : Int,
  “ (retval = (0 : Int)) ” &&
  “ ¬((FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval = (0 : Int)) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int)))))
  ||
  (EX retval_2 : Int,
  “ (retval_2 = (0 : Int)) ” &&
  “ ¬((FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval_2 = (0 : Int)) ”
  &&  (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int)))))
  ||
  (EX retval_3 : Int,
  “ (retval_3 = (0 : Int)) ” &&
  “ ¬((FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval_3 = (0 : Int)) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int)))))
  ||
  (EX retval_4 : Int,
  “ (retval_4 = (0 : Int)) ” &&
  “ ¬((FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval_4 = (0 : Int)) ”
  &&  (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int)))))

noncomputable def solver_entail_wit_5_5 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval_3 : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval_3 = (0 : Int))) (PreH2 : ¬((FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre))) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval_3 = (0 : Int))) ,
  (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
|--
  “ (retval_3 = (0 : Int)) ” &&
  “ ¬((FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval_3 = (0 : Int)) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))

noncomputable def solver_entail_wit_5_6 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval_5 : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval_5 = 1)) (PreH2 : (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval_5 = (0 : Int))) ,
  (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
|--
  (EX retval : Int,
  “ (retval = (0 : Int)) ” &&
  “ ¬((FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval = (0 : Int)) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int)))))
  ||
  (EX retval_2 : Int,
  “ (retval_2 = (0 : Int)) ” &&
  “ ¬((FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval_2 = (0 : Int)) ”
  &&  (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int)))))
  ||
  (EX retval_3 : Int,
  “ (retval_3 = (0 : Int)) ” &&
  “ ¬((FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval_3 = (0 : Int)) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int)))))
  ||
  (EX retval_4 : Int,
  “ (retval_4 = (0 : Int)) ” &&
  “ ¬((FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval_4 = (0 : Int)) ”
  &&  (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int)))))

noncomputable def solver_entail_wit_5_7 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval_4 : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval_4 = (0 : Int))) (PreH2 : ¬((FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre))) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval_4 = (0 : Int))) ,
  (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
|--
  “ (retval_4 = (0 : Int)) ” &&
  “ ¬((FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval_4 = (0 : Int)) ”
  &&  (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))

noncomputable def solver_entail_wit_5_8 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval_5 : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval_5 = 1)) (PreH2 : (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval_5 = (0 : Int))) ,
  (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
|--
  (EX retval : Int,
  “ (retval = (0 : Int)) ” &&
  “ ¬((FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval = (0 : Int)) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int)))))
  ||
  (EX retval_2 : Int,
  “ (retval_2 = (0 : Int)) ” &&
  “ ¬((FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval_2 = (0 : Int)) ”
  &&  (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int)))))
  ||
  (EX retval_3 : Int,
  “ (retval_3 = (0 : Int)) ” &&
  “ ¬((FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval_3 = (0 : Int)) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int)))))
  ||
  (EX retval_4 : Int,
  “ (retval_4 = (0 : Int)) ” &&
  “ ¬((FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval_4 = (0 : Int)) ”
  &&  (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int)))))

noncomputable def solver_entail_wit_6_1 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval_5 : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval_5 = (0 : Int))) (PreH2 : ¬((FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre))) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval_5 ≠ (0 : Int))) ,
  (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
|--
  (EX retval : Int,
  “ (retval = 1) ” &&
  “ (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval ≠ (0 : Int)) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int)))))
  ||
  (EX retval_2 : Int,
  “ (retval_2 = 1) ” &&
  “ (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval_2 ≠ (0 : Int)) ”
  &&  (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int)))))
  ||
  (EX retval_3 : Int,
  “ (retval_3 = 1) ” &&
  “ (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval_3 ≠ (0 : Int)) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int)))))
  ||
  (EX retval_4 : Int,
  “ (retval_4 = 1) ” &&
  “ (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval_4 ≠ (0 : Int)) ”
  &&  (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int)))))

noncomputable def solver_entail_wit_6_2 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval ≠ (0 : Int))) ,
  (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
|--
  “ (retval = 1) ” &&
  “ (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval ≠ (0 : Int)) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))

noncomputable def solver_entail_wit_6_3 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval_5 : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval_5 = (0 : Int))) (PreH2 : ¬((FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre))) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval_5 ≠ (0 : Int))) ,
  (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
|--
  (EX retval : Int,
  “ (retval = 1) ” &&
  “ (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval ≠ (0 : Int)) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int)))))
  ||
  (EX retval_2 : Int,
  “ (retval_2 = 1) ” &&
  “ (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval_2 ≠ (0 : Int)) ”
  &&  (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int)))))
  ||
  (EX retval_3 : Int,
  “ (retval_3 = 1) ” &&
  “ (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval_3 ≠ (0 : Int)) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int)))))
  ||
  (EX retval_4 : Int,
  “ (retval_4 = 1) ” &&
  “ (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval_4 ≠ (0 : Int)) ”
  &&  (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int)))))

noncomputable def solver_entail_wit_6_4 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval_2 : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval_2 = 1)) (PreH2 : (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval_2 ≠ (0 : Int))) ,
  (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
|--
  “ (retval_2 = 1) ” &&
  “ (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval_2 ≠ (0 : Int)) ”
  &&  (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))

noncomputable def solver_entail_wit_6_5 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval_5 : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval_5 = (0 : Int))) (PreH2 : ¬((FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre))) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval_5 ≠ (0 : Int))) ,
  (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
|--
  (EX retval : Int,
  “ (retval = 1) ” &&
  “ (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval ≠ (0 : Int)) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int)))))
  ||
  (EX retval_2 : Int,
  “ (retval_2 = 1) ” &&
  “ (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval_2 ≠ (0 : Int)) ”
  &&  (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int)))))
  ||
  (EX retval_3 : Int,
  “ (retval_3 = 1) ” &&
  “ (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval_3 ≠ (0 : Int)) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int)))))
  ||
  (EX retval_4 : Int,
  “ (retval_4 = 1) ” &&
  “ (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval_4 ≠ (0 : Int)) ”
  &&  (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int)))))

noncomputable def solver_entail_wit_6_6 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval_3 : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval_3 = 1)) (PreH2 : (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval_3 ≠ (0 : Int))) ,
  (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
|--
  “ (retval_3 = 1) ” &&
  “ (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval_3 ≠ (0 : Int)) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))

noncomputable def solver_entail_wit_6_7 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval_5 : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval_5 = (0 : Int))) (PreH2 : ¬((FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre))) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval_5 ≠ (0 : Int))) ,
  (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
|--
  (EX retval : Int,
  “ (retval = 1) ” &&
  “ (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval ≠ (0 : Int)) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int)))))
  ||
  (EX retval_2 : Int,
  “ (retval_2 = 1) ” &&
  “ (FitsDims (Znth i ys_spec (0 : Int)) (Znth i xs_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval_2 ≠ (0 : Int)) ”
  &&  (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int)))))
  ||
  (EX retval_3 : Int,
  “ (retval_3 = 1) ” &&
  “ (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) a_pre b_pre) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval_3 ≠ (0 : Int)) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int)))))
  ||
  (EX retval_4 : Int,
  “ (retval_4 = 1) ” &&
  “ (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval_4 ≠ (0 : Int)) ”
  &&  (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int)))))

noncomputable def solver_entail_wit_6_8 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (retval_4 : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval_4 = 1)) (PreH2 : (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre)) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval_4 ≠ (0 : Int))) ,
  (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
|--
  “ (retval_4 = 1) ” &&
  “ (FitsDims (Znth i xs_spec (0 : Int)) (Znth i ys_spec (0 : Int)) (Znth j xs_spec (0 : Int)) (Znth j ys_spec (0 : Int)) a_pre b_pre) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ” &&
  “ (retval_4 ≠ (0 : Int)) ”
  &&  (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))

noncomputable def solver_entail_wit_7 : Prop :=
  (
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (j >= n_pre)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k_2 xs_spec_2 (0 : Int)) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((Znth k_2 ys_spec_2 (0 : Int)) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((i + 1) <= j)) (PreH17 : (j <= n_pre)) (PreH18 : ((0 : Int) <= best)) (PreH19 : (best <= 20000)) (PreH20 : (BestBefore paper seals i j (0 : Int) (0 : Int) best)) ,
  (intArray.full x_pre n_pre xs_spec_2)
  ** (intArray.full y_pre n_pre ys_spec_2)
|--
  EX ys_spec : (List Int), EX xs_spec : (List Int),
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals (i + 1) ((i + 1) + 1) (0 : Int) (0 : Int) best) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
) \/
(
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (j >= n_pre)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k_2 xs_spec_2 (0 : Int)) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((Znth k_2 ys_spec_2 (0 : Int)) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((i + 1) <= j)) (PreH17 : (j <= n_pre)) (PreH18 : ((0 : Int) <= best)) (PreH19 : (best <= 20000)) (PreH20 : (BestBefore paper seals i j (0 : Int) (0 : Int) best)) ,
  TT && emp 
|--
  “ (BestBefore paper seals (i + 1) ((i + 1) + 1) (0 : Int) (0 : Int) best) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ”
  &&  emp
)

noncomputable def solver_entail_wit_7_split_goal_1 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (j >= n_pre)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k_2 xs_spec_2 (0 : Int)) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((Znth k_2 ys_spec_2 (0 : Int)) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((i + 1) <= j)) (PreH17 : (j <= n_pre)) (PreH18 : ((0 : Int) <= best)) (PreH19 : (best <= 20000)) (PreH20 : (BestBefore paper seals i j (0 : Int) (0 : Int) best)) ,
  (BestBefore paper seals (i + 1) ((i + 1) + 1) (0 : Int) (0 : Int) best)

noncomputable def solver_entail_wit_7_split_goal_2 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (j >= n_pre)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k_2 xs_spec_2 (0 : Int)) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((Znth k_2 ys_spec_2 (0 : Int)) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((i + 1) <= j)) (PreH17 : (j <= n_pre)) (PreH18 : ((0 : Int) <= best)) (PreH19 : (best <= 20000)) (PreH20 : (BestBefore paper seals i j (0 : Int) (0 : Int) best)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))

noncomputable def solver_entail_wit_8 : Prop :=
  (
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (ri >= 2)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k_2 xs_spec_2 (0 : Int)) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((Znth k_2 ys_spec_2 (0 : Int)) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < j)) (PreH16 : (j < n_pre)) (PreH17 : ((0 : Int) <= ri)) (PreH18 : (ri <= 2)) (PreH19 : ((0 : Int) <= best)) (PreH20 : (best <= 20000)) (PreH21 : (BestBefore paper seals i j ri (0 : Int) best)) ,
  (intArray.full x_pre n_pre xs_spec_2)
  ** (intArray.full y_pre n_pre ys_spec_2)
|--
  EX ys_spec : (List Int), EX xs_spec : (List Int),
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((i + 1) <= (j + 1)) ” &&
  “ ((j + 1) <= n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i (j + 1) (0 : Int) (0 : Int) best) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
) \/
(
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (ri >= 2)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k_2 xs_spec_2 (0 : Int)) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((Znth k_2 ys_spec_2 (0 : Int)) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < j)) (PreH16 : (j < n_pre)) (PreH17 : ((0 : Int) <= ri)) (PreH18 : (ri <= 2)) (PreH19 : ((0 : Int) <= best)) (PreH20 : (best <= 20000)) (PreH21 : (BestBefore paper seals i j ri (0 : Int) best)) ,
  TT && emp 
|--
  “ (BestBefore paper seals i (j + 1) (0 : Int) (0 : Int) best) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ”
  &&  emp
)

noncomputable def solver_entail_wit_8_split_goal_1 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (ri >= 2)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k_2 xs_spec_2 (0 : Int)) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((Znth k_2 ys_spec_2 (0 : Int)) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < j)) (PreH16 : (j < n_pre)) (PreH17 : ((0 : Int) <= ri)) (PreH18 : (ri <= 2)) (PreH19 : ((0 : Int) <= best)) (PreH20 : (best <= 20000)) (PreH21 : (BestBefore paper seals i j ri (0 : Int) best)) ,
  (BestBefore paper seals i (j + 1) (0 : Int) (0 : Int) best)

noncomputable def solver_entail_wit_8_split_goal_2 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (ri >= 2)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k_2 xs_spec_2 (0 : Int)) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((Znth k_2 ys_spec_2 (0 : Int)) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < j)) (PreH16 : (j < n_pre)) (PreH17 : ((0 : Int) <= ri)) (PreH18 : (ri <= 2)) (PreH19 : ((0 : Int) <= best)) (PreH20 : (best <= 20000)) (PreH21 : (BestBefore paper seals i j ri (0 : Int) best)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))

noncomputable def solver_entail_wit_9 : Prop :=
  (
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (rj >= 2)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k_2 xs_spec_2 (0 : Int)) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((Znth k_2 ys_spec_2 (0 : Int)) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < j)) (PreH16 : (j < n_pre)) (PreH17 : ((0 : Int) <= ri)) (PreH18 : (ri < 2)) (PreH19 : ((0 : Int) <= rj)) (PreH20 : (rj <= 2)) (PreH21 : ((0 : Int) <= best)) (PreH22 : (best <= 20000)) (PreH23 : (BestBefore paper seals i j ri rj best)) ,
  (intArray.full x_pre n_pre xs_spec_2)
  ** (intArray.full y_pre n_pre ys_spec_2)
|--
  EX ys_spec : (List Int), EX xs_spec : (List Int),
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= (ri + 1)) ” &&
  “ ((ri + 1) <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j (ri + 1) (0 : Int) best) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
) \/
(
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (rj >= 2)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k_2 xs_spec_2 (0 : Int)) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((Znth k_2 ys_spec_2 (0 : Int)) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < j)) (PreH16 : (j < n_pre)) (PreH17 : ((0 : Int) <= ri)) (PreH18 : (ri < 2)) (PreH19 : ((0 : Int) <= rj)) (PreH20 : (rj <= 2)) (PreH21 : ((0 : Int) <= best)) (PreH22 : (best <= 20000)) (PreH23 : (BestBefore paper seals i j ri rj best)) ,
  TT && emp 
|--
  “ (BestBefore paper seals i j (ri + 1) (0 : Int) best) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ”
  &&  emp
)

noncomputable def solver_entail_wit_9_split_goal_1 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (rj >= 2)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k_2 xs_spec_2 (0 : Int)) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((Znth k_2 ys_spec_2 (0 : Int)) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < j)) (PreH16 : (j < n_pre)) (PreH17 : ((0 : Int) <= ri)) (PreH18 : (ri < 2)) (PreH19 : ((0 : Int) <= rj)) (PreH20 : (rj <= 2)) (PreH21 : ((0 : Int) <= best)) (PreH22 : (best <= 20000)) (PreH23 : (BestBefore paper seals i j ri rj best)) ,
  (BestBefore paper seals i j (ri + 1) (0 : Int) best)

noncomputable def solver_entail_wit_9_split_goal_2 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (rj >= 2)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k_2 xs_spec_2 (0 : Int)) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) ∧ ((Znth k_2 ys_spec_2 (0 : Int)) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < j)) (PreH16 : (j < n_pre)) (PreH17 : ((0 : Int) <= ri)) (PreH18 : (ri < 2)) (PreH19 : ((0 : Int) <= rj)) (PreH20 : (rj <= 2)) (PreH21 : ((0 : Int) <= best)) (PreH22 : (best <= 20000)) (PreH23 : (BestBefore paper seals i j ri rj best)) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))

noncomputable def solver_entail_wit_10_1 : Prop :=
  (
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : ((((Znth i ys_spec_2 (0 : Int)) * (Znth i xs_spec_2 (0 : Int))) + ((Znth j ys_spec_2 (0 : Int)) * (Znth j xs_spec_2 (0 : Int)))) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i ys_spec_2 (0 : Int)) (Znth i xs_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) a_pre b_pre)) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (rj ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (ri ≠ (0 : Int))) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : ((0 : Int) <= ri)) (PreH25 : (ri < 2)) (PreH26 : ((0 : Int) <= rj)) (PreH27 : (rj <= 2)) (PreH28 : ((0 : Int) <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best)) (PreH31 : (retval ≠ (0 : Int))) ,
  (intArray.full x_pre n_pre xs_spec_2)
  ** (intArray.full y_pre n_pre ys_spec_2)
|--
  EX ys_spec : (List Int), EX xs_spec : (List Int),
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= (rj + 1)) ” &&
  “ ((rj + 1) <= 2) ” &&
  “ ((0 : Int) <= (((Znth i ys_spec_2 (0 : Int)) * (Znth i xs_spec_2 (0 : Int))) + ((Znth j ys_spec_2 (0 : Int)) * (Znth j xs_spec_2 (0 : Int))))) ” &&
  “ ((((Znth i ys_spec_2 (0 : Int)) * (Znth i xs_spec_2 (0 : Int))) + ((Znth j ys_spec_2 (0 : Int)) * (Znth j xs_spec_2 (0 : Int)))) <= 20000) ” &&
  “ (BestBefore paper seals i j ri (rj + 1) (((Znth i ys_spec_2 (0 : Int)) * (Znth i xs_spec_2 (0 : Int))) + ((Znth j ys_spec_2 (0 : Int)) * (Znth j xs_spec_2 (0 : Int))))) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
) \/
(
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : ((((Znth i ys_spec_2 (0 : Int)) * (Znth i xs_spec_2 (0 : Int))) + ((Znth j ys_spec_2 (0 : Int)) * (Znth j xs_spec_2 (0 : Int)))) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i ys_spec_2 (0 : Int)) (Znth i xs_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) a_pre b_pre)) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (rj ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (ri ≠ (0 : Int))) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : ((0 : Int) <= ri)) (PreH25 : (ri < 2)) (PreH26 : ((0 : Int) <= rj)) (PreH27 : (rj <= 2)) (PreH28 : ((0 : Int) <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best)) (PreH31 : (retval ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (BestBefore paper seals i j ri (rj + 1) (((Znth i ys_spec_2 (0 : Int)) * (Znth i xs_spec_2 (0 : Int))) + ((Znth j ys_spec_2 (0 : Int)) * (Znth j xs_spec_2 (0 : Int))))) ” &&
  “ ((((Znth i ys_spec_2 (0 : Int)) * (Znth i xs_spec_2 (0 : Int))) + ((Znth j ys_spec_2 (0 : Int)) * (Znth j xs_spec_2 (0 : Int)))) <= 20000) ”
  &&  emp
)

noncomputable def solver_entail_wit_10_1_split_goal_1 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : ((((Znth i ys_spec_2 (0 : Int)) * (Znth i xs_spec_2 (0 : Int))) + ((Znth j ys_spec_2 (0 : Int)) * (Znth j xs_spec_2 (0 : Int)))) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i ys_spec_2 (0 : Int)) (Znth i xs_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) a_pre b_pre)) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (rj ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (ri ≠ (0 : Int))) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : ((0 : Int) <= ri)) (PreH25 : (ri < 2)) (PreH26 : ((0 : Int) <= rj)) (PreH27 : (rj <= 2)) (PreH28 : ((0 : Int) <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best)) (PreH31 : (retval ≠ (0 : Int))) ,
  (BestBefore paper seals i j ri (rj + 1) (((Znth i ys_spec_2 (0 : Int)) * (Znth i xs_spec_2 (0 : Int))) + ((Znth j ys_spec_2 (0 : Int)) * (Znth j xs_spec_2 (0 : Int)))))

noncomputable def solver_entail_wit_10_1_split_goal_2 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : ((((Znth i ys_spec_2 (0 : Int)) * (Znth i xs_spec_2 (0 : Int))) + ((Znth j ys_spec_2 (0 : Int)) * (Znth j xs_spec_2 (0 : Int)))) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i ys_spec_2 (0 : Int)) (Znth i xs_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) a_pre b_pre)) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (rj ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (ri ≠ (0 : Int))) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : ((0 : Int) <= ri)) (PreH25 : (ri < 2)) (PreH26 : ((0 : Int) <= rj)) (PreH27 : (rj <= 2)) (PreH28 : ((0 : Int) <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best)) (PreH31 : (retval ≠ (0 : Int))) ,
  ((((Znth i ys_spec_2 (0 : Int)) * (Znth i xs_spec_2 (0 : Int))) + ((Znth j ys_spec_2 (0 : Int)) * (Znth j xs_spec_2 (0 : Int)))) <= 20000)

noncomputable def solver_entail_wit_10_2 : Prop :=
  (
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : ((((Znth i ys_spec_2 (0 : Int)) * (Znth i xs_spec_2 (0 : Int))) + ((Znth j xs_spec_2 (0 : Int)) * (Znth j ys_spec_2 (0 : Int)))) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i ys_spec_2 (0 : Int)) (Znth i xs_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) a_pre b_pre)) (PreH4 : (rj = (0 : Int))) (PreH5 : (rj = (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (ri ≠ (0 : Int))) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : ((0 : Int) <= ri)) (PreH25 : (ri < 2)) (PreH26 : ((0 : Int) <= rj)) (PreH27 : (rj <= 2)) (PreH28 : ((0 : Int) <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best)) (PreH31 : (retval ≠ (0 : Int))) ,
  (intArray.full y_pre n_pre ys_spec_2)
  ** (intArray.full x_pre n_pre xs_spec_2)
|--
  EX ys_spec : (List Int), EX xs_spec : (List Int),
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= (rj + 1)) ” &&
  “ ((rj + 1) <= 2) ” &&
  “ ((0 : Int) <= (((Znth i ys_spec_2 (0 : Int)) * (Znth i xs_spec_2 (0 : Int))) + ((Znth j xs_spec_2 (0 : Int)) * (Znth j ys_spec_2 (0 : Int))))) ” &&
  “ ((((Znth i ys_spec_2 (0 : Int)) * (Znth i xs_spec_2 (0 : Int))) + ((Znth j xs_spec_2 (0 : Int)) * (Znth j ys_spec_2 (0 : Int)))) <= 20000) ” &&
  “ (BestBefore paper seals i j ri (rj + 1) (((Znth i ys_spec_2 (0 : Int)) * (Znth i xs_spec_2 (0 : Int))) + ((Znth j xs_spec_2 (0 : Int)) * (Znth j ys_spec_2 (0 : Int))))) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
) \/
(
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : ((((Znth i ys_spec_2 (0 : Int)) * (Znth i xs_spec_2 (0 : Int))) + ((Znth j xs_spec_2 (0 : Int)) * (Znth j ys_spec_2 (0 : Int)))) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i ys_spec_2 (0 : Int)) (Znth i xs_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) a_pre b_pre)) (PreH4 : (rj = (0 : Int))) (PreH5 : (rj = (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (ri ≠ (0 : Int))) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : ((0 : Int) <= ri)) (PreH25 : (ri < 2)) (PreH26 : ((0 : Int) <= rj)) (PreH27 : (rj <= 2)) (PreH28 : ((0 : Int) <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best)) (PreH31 : (retval ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (BestBefore paper seals i j ri ((0 : Int) + 1) (((Znth i ys_spec_2 (0 : Int)) * (Znth i xs_spec_2 (0 : Int))) + ((Znth j xs_spec_2 (0 : Int)) * (Znth j ys_spec_2 (0 : Int))))) ” &&
  “ ((((Znth i ys_spec_2 (0 : Int)) * (Znth i xs_spec_2 (0 : Int))) + ((Znth j xs_spec_2 (0 : Int)) * (Znth j ys_spec_2 (0 : Int)))) <= 20000) ”
  &&  emp
)

noncomputable def solver_entail_wit_10_2_split_goal_1 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : ((((Znth i ys_spec_2 (0 : Int)) * (Znth i xs_spec_2 (0 : Int))) + ((Znth j xs_spec_2 (0 : Int)) * (Znth j ys_spec_2 (0 : Int)))) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i ys_spec_2 (0 : Int)) (Znth i xs_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) a_pre b_pre)) (PreH4 : (rj = (0 : Int))) (PreH5 : (rj = (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (ri ≠ (0 : Int))) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : ((0 : Int) <= ri)) (PreH25 : (ri < 2)) (PreH26 : ((0 : Int) <= rj)) (PreH27 : (rj <= 2)) (PreH28 : ((0 : Int) <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best)) (PreH31 : (retval ≠ (0 : Int))) ,
  (BestBefore paper seals i j ri ((0 : Int) + 1) (((Znth i ys_spec_2 (0 : Int)) * (Znth i xs_spec_2 (0 : Int))) + ((Znth j xs_spec_2 (0 : Int)) * (Znth j ys_spec_2 (0 : Int)))))

noncomputable def solver_entail_wit_10_2_split_goal_2 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : ((((Znth i ys_spec_2 (0 : Int)) * (Znth i xs_spec_2 (0 : Int))) + ((Znth j xs_spec_2 (0 : Int)) * (Znth j ys_spec_2 (0 : Int)))) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i ys_spec_2 (0 : Int)) (Znth i xs_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) a_pre b_pre)) (PreH4 : (rj = (0 : Int))) (PreH5 : (rj = (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (ri ≠ (0 : Int))) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : ((0 : Int) <= ri)) (PreH25 : (ri < 2)) (PreH26 : ((0 : Int) <= rj)) (PreH27 : (rj <= 2)) (PreH28 : ((0 : Int) <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best)) (PreH31 : (retval ≠ (0 : Int))) ,
  ((((Znth i ys_spec_2 (0 : Int)) * (Znth i xs_spec_2 (0 : Int))) + ((Znth j xs_spec_2 (0 : Int)) * (Znth j ys_spec_2 (0 : Int)))) <= 20000)

noncomputable def solver_entail_wit_10_3 : Prop :=
  (
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : ((((Znth i xs_spec_2 (0 : Int)) * (Znth i ys_spec_2 (0 : Int))) + ((Znth j ys_spec_2 (0 : Int)) * (Znth j xs_spec_2 (0 : Int)))) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i xs_spec_2 (0 : Int)) (Znth i ys_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) a_pre b_pre)) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (rj ≠ (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (ri = (0 : Int))) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : ((0 : Int) <= ri)) (PreH25 : (ri < 2)) (PreH26 : ((0 : Int) <= rj)) (PreH27 : (rj <= 2)) (PreH28 : ((0 : Int) <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best)) (PreH31 : (retval ≠ (0 : Int))) ,
  (intArray.full x_pre n_pre xs_spec_2)
  ** (intArray.full y_pre n_pre ys_spec_2)
|--
  EX ys_spec : (List Int), EX xs_spec : (List Int),
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= (rj + 1)) ” &&
  “ ((rj + 1) <= 2) ” &&
  “ ((0 : Int) <= (((Znth i xs_spec_2 (0 : Int)) * (Znth i ys_spec_2 (0 : Int))) + ((Znth j ys_spec_2 (0 : Int)) * (Znth j xs_spec_2 (0 : Int))))) ” &&
  “ ((((Znth i xs_spec_2 (0 : Int)) * (Znth i ys_spec_2 (0 : Int))) + ((Znth j ys_spec_2 (0 : Int)) * (Znth j xs_spec_2 (0 : Int)))) <= 20000) ” &&
  “ (BestBefore paper seals i j ri (rj + 1) (((Znth i xs_spec_2 (0 : Int)) * (Znth i ys_spec_2 (0 : Int))) + ((Znth j ys_spec_2 (0 : Int)) * (Znth j xs_spec_2 (0 : Int))))) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
) \/
(
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : ((((Znth i xs_spec_2 (0 : Int)) * (Znth i ys_spec_2 (0 : Int))) + ((Znth j ys_spec_2 (0 : Int)) * (Znth j xs_spec_2 (0 : Int)))) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i xs_spec_2 (0 : Int)) (Znth i ys_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) a_pre b_pre)) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (rj ≠ (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (ri = (0 : Int))) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : ((0 : Int) <= ri)) (PreH25 : (ri < 2)) (PreH26 : ((0 : Int) <= rj)) (PreH27 : (rj <= 2)) (PreH28 : ((0 : Int) <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best)) (PreH31 : (retval ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (BestBefore paper seals i j (0 : Int) (rj + 1) (((Znth i xs_spec_2 (0 : Int)) * (Znth i ys_spec_2 (0 : Int))) + ((Znth j ys_spec_2 (0 : Int)) * (Znth j xs_spec_2 (0 : Int))))) ” &&
  “ ((((Znth i xs_spec_2 (0 : Int)) * (Znth i ys_spec_2 (0 : Int))) + ((Znth j ys_spec_2 (0 : Int)) * (Znth j xs_spec_2 (0 : Int)))) <= 20000) ”
  &&  emp
)

noncomputable def solver_entail_wit_10_3_split_goal_1 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : ((((Znth i xs_spec_2 (0 : Int)) * (Znth i ys_spec_2 (0 : Int))) + ((Znth j ys_spec_2 (0 : Int)) * (Znth j xs_spec_2 (0 : Int)))) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i xs_spec_2 (0 : Int)) (Znth i ys_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) a_pre b_pre)) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (rj ≠ (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (ri = (0 : Int))) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : ((0 : Int) <= ri)) (PreH25 : (ri < 2)) (PreH26 : ((0 : Int) <= rj)) (PreH27 : (rj <= 2)) (PreH28 : ((0 : Int) <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best)) (PreH31 : (retval ≠ (0 : Int))) ,
  (BestBefore paper seals i j (0 : Int) (rj + 1) (((Znth i xs_spec_2 (0 : Int)) * (Znth i ys_spec_2 (0 : Int))) + ((Znth j ys_spec_2 (0 : Int)) * (Znth j xs_spec_2 (0 : Int)))))

noncomputable def solver_entail_wit_10_3_split_goal_2 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : ((((Znth i xs_spec_2 (0 : Int)) * (Znth i ys_spec_2 (0 : Int))) + ((Znth j ys_spec_2 (0 : Int)) * (Znth j xs_spec_2 (0 : Int)))) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i xs_spec_2 (0 : Int)) (Znth i ys_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) a_pre b_pre)) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (rj ≠ (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (ri = (0 : Int))) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : ((0 : Int) <= ri)) (PreH25 : (ri < 2)) (PreH26 : ((0 : Int) <= rj)) (PreH27 : (rj <= 2)) (PreH28 : ((0 : Int) <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best)) (PreH31 : (retval ≠ (0 : Int))) ,
  ((((Znth i xs_spec_2 (0 : Int)) * (Znth i ys_spec_2 (0 : Int))) + ((Znth j ys_spec_2 (0 : Int)) * (Znth j xs_spec_2 (0 : Int)))) <= 20000)

noncomputable def solver_entail_wit_10_4 : Prop :=
  (
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : ((((Znth i xs_spec_2 (0 : Int)) * (Znth i ys_spec_2 (0 : Int))) + ((Znth j xs_spec_2 (0 : Int)) * (Znth j ys_spec_2 (0 : Int)))) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i xs_spec_2 (0 : Int)) (Znth i ys_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) a_pre b_pre)) (PreH4 : (rj = (0 : Int))) (PreH5 : (rj = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (ri = (0 : Int))) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : ((0 : Int) <= ri)) (PreH25 : (ri < 2)) (PreH26 : ((0 : Int) <= rj)) (PreH27 : (rj <= 2)) (PreH28 : ((0 : Int) <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best)) (PreH31 : (retval ≠ (0 : Int))) ,
  (intArray.full y_pre n_pre ys_spec_2)
  ** (intArray.full x_pre n_pre xs_spec_2)
|--
  EX ys_spec : (List Int), EX xs_spec : (List Int),
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= (rj + 1)) ” &&
  “ ((rj + 1) <= 2) ” &&
  “ ((0 : Int) <= (((Znth i xs_spec_2 (0 : Int)) * (Znth i ys_spec_2 (0 : Int))) + ((Znth j xs_spec_2 (0 : Int)) * (Znth j ys_spec_2 (0 : Int))))) ” &&
  “ ((((Znth i xs_spec_2 (0 : Int)) * (Znth i ys_spec_2 (0 : Int))) + ((Znth j xs_spec_2 (0 : Int)) * (Znth j ys_spec_2 (0 : Int)))) <= 20000) ” &&
  “ (BestBefore paper seals i j ri (rj + 1) (((Znth i xs_spec_2 (0 : Int)) * (Znth i ys_spec_2 (0 : Int))) + ((Znth j xs_spec_2 (0 : Int)) * (Znth j ys_spec_2 (0 : Int))))) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
) \/
(
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : ((((Znth i xs_spec_2 (0 : Int)) * (Znth i ys_spec_2 (0 : Int))) + ((Znth j xs_spec_2 (0 : Int)) * (Znth j ys_spec_2 (0 : Int)))) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i xs_spec_2 (0 : Int)) (Znth i ys_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) a_pre b_pre)) (PreH4 : (rj = (0 : Int))) (PreH5 : (rj = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (ri = (0 : Int))) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : ((0 : Int) <= ri)) (PreH25 : (ri < 2)) (PreH26 : ((0 : Int) <= rj)) (PreH27 : (rj <= 2)) (PreH28 : ((0 : Int) <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best)) (PreH31 : (retval ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (BestBefore paper seals i j (0 : Int) ((0 : Int) + 1) (((Znth i xs_spec_2 (0 : Int)) * (Znth i ys_spec_2 (0 : Int))) + ((Znth j xs_spec_2 (0 : Int)) * (Znth j ys_spec_2 (0 : Int))))) ” &&
  “ ((((Znth i xs_spec_2 (0 : Int)) * (Znth i ys_spec_2 (0 : Int))) + ((Znth j xs_spec_2 (0 : Int)) * (Znth j ys_spec_2 (0 : Int)))) <= 20000) ”
  &&  emp
)

noncomputable def solver_entail_wit_10_4_split_goal_1 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : ((((Znth i xs_spec_2 (0 : Int)) * (Znth i ys_spec_2 (0 : Int))) + ((Znth j xs_spec_2 (0 : Int)) * (Znth j ys_spec_2 (0 : Int)))) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i xs_spec_2 (0 : Int)) (Znth i ys_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) a_pre b_pre)) (PreH4 : (rj = (0 : Int))) (PreH5 : (rj = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (ri = (0 : Int))) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : ((0 : Int) <= ri)) (PreH25 : (ri < 2)) (PreH26 : ((0 : Int) <= rj)) (PreH27 : (rj <= 2)) (PreH28 : ((0 : Int) <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best)) (PreH31 : (retval ≠ (0 : Int))) ,
  (BestBefore paper seals i j (0 : Int) ((0 : Int) + 1) (((Znth i xs_spec_2 (0 : Int)) * (Znth i ys_spec_2 (0 : Int))) + ((Znth j xs_spec_2 (0 : Int)) * (Znth j ys_spec_2 (0 : Int)))))

noncomputable def solver_entail_wit_10_4_split_goal_2 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : ((((Znth i xs_spec_2 (0 : Int)) * (Znth i ys_spec_2 (0 : Int))) + ((Znth j xs_spec_2 (0 : Int)) * (Znth j ys_spec_2 (0 : Int)))) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i xs_spec_2 (0 : Int)) (Znth i ys_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) a_pre b_pre)) (PreH4 : (rj = (0 : Int))) (PreH5 : (rj = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (ri = (0 : Int))) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : ((0 : Int) <= ri)) (PreH25 : (ri < 2)) (PreH26 : ((0 : Int) <= rj)) (PreH27 : (rj <= 2)) (PreH28 : ((0 : Int) <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best)) (PreH31 : (retval ≠ (0 : Int))) ,
  ((((Znth i xs_spec_2 (0 : Int)) * (Znth i ys_spec_2 (0 : Int))) + ((Znth j xs_spec_2 (0 : Int)) * (Znth j ys_spec_2 (0 : Int)))) <= 20000)

noncomputable def solver_entail_wit_10_5 : Prop :=
  (
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : ((((Znth i ys_spec_2 (0 : Int)) * (Znth i xs_spec_2 (0 : Int))) + ((Znth j ys_spec_2 (0 : Int)) * (Znth j xs_spec_2 (0 : Int)))) <= best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i ys_spec_2 (0 : Int)) (Znth i xs_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) a_pre b_pre)) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (rj ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (ri ≠ (0 : Int))) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : ((0 : Int) <= ri)) (PreH25 : (ri < 2)) (PreH26 : ((0 : Int) <= rj)) (PreH27 : (rj <= 2)) (PreH28 : ((0 : Int) <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best)) (PreH31 : (retval ≠ (0 : Int))) ,
  (intArray.full x_pre n_pre xs_spec_2)
  ** (intArray.full y_pre n_pre ys_spec_2)
|--
  EX ys_spec : (List Int), EX xs_spec : (List Int),
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= (rj + 1)) ” &&
  “ ((rj + 1) <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri (rj + 1) best) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
) \/
(
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : ((((Znth i ys_spec_2 (0 : Int)) * (Znth i xs_spec_2 (0 : Int))) + ((Znth j ys_spec_2 (0 : Int)) * (Znth j xs_spec_2 (0 : Int)))) <= best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i ys_spec_2 (0 : Int)) (Znth i xs_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) a_pre b_pre)) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (rj ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (ri ≠ (0 : Int))) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : ((0 : Int) <= ri)) (PreH25 : (ri < 2)) (PreH26 : ((0 : Int) <= rj)) (PreH27 : (rj <= 2)) (PreH28 : ((0 : Int) <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best)) (PreH31 : (retval ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (BestBefore paper seals i j ri (rj + 1) best) ”
  &&  emp
)

noncomputable def solver_entail_wit_10_5_split_goal_1 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : ((((Znth i ys_spec_2 (0 : Int)) * (Znth i xs_spec_2 (0 : Int))) + ((Znth j ys_spec_2 (0 : Int)) * (Znth j xs_spec_2 (0 : Int)))) <= best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i ys_spec_2 (0 : Int)) (Znth i xs_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) a_pre b_pre)) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (rj ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (ri ≠ (0 : Int))) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : ((0 : Int) <= ri)) (PreH25 : (ri < 2)) (PreH26 : ((0 : Int) <= rj)) (PreH27 : (rj <= 2)) (PreH28 : ((0 : Int) <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best)) (PreH31 : (retval ≠ (0 : Int))) ,
  (BestBefore paper seals i j ri (rj + 1) best)

noncomputable def solver_entail_wit_10_6 : Prop :=
  (
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : ((((Znth i ys_spec_2 (0 : Int)) * (Znth i xs_spec_2 (0 : Int))) + ((Znth j xs_spec_2 (0 : Int)) * (Znth j ys_spec_2 (0 : Int)))) <= best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i ys_spec_2 (0 : Int)) (Znth i xs_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) a_pre b_pre)) (PreH4 : (rj = (0 : Int))) (PreH5 : (rj = (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (ri ≠ (0 : Int))) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : ((0 : Int) <= ri)) (PreH25 : (ri < 2)) (PreH26 : ((0 : Int) <= rj)) (PreH27 : (rj <= 2)) (PreH28 : ((0 : Int) <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best)) (PreH31 : (retval ≠ (0 : Int))) ,
  (intArray.full y_pre n_pre ys_spec_2)
  ** (intArray.full x_pre n_pre xs_spec_2)
|--
  EX ys_spec : (List Int), EX xs_spec : (List Int),
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= (rj + 1)) ” &&
  “ ((rj + 1) <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri (rj + 1) best) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
) \/
(
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : ((((Znth i ys_spec_2 (0 : Int)) * (Znth i xs_spec_2 (0 : Int))) + ((Znth j xs_spec_2 (0 : Int)) * (Znth j ys_spec_2 (0 : Int)))) <= best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i ys_spec_2 (0 : Int)) (Znth i xs_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) a_pre b_pre)) (PreH4 : (rj = (0 : Int))) (PreH5 : (rj = (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (ri ≠ (0 : Int))) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : ((0 : Int) <= ri)) (PreH25 : (ri < 2)) (PreH26 : ((0 : Int) <= rj)) (PreH27 : (rj <= 2)) (PreH28 : ((0 : Int) <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best)) (PreH31 : (retval ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (BestBefore paper seals i j ri ((0 : Int) + 1) best) ”
  &&  emp
)

noncomputable def solver_entail_wit_10_6_split_goal_1 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : ((((Znth i ys_spec_2 (0 : Int)) * (Znth i xs_spec_2 (0 : Int))) + ((Znth j xs_spec_2 (0 : Int)) * (Znth j ys_spec_2 (0 : Int)))) <= best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i ys_spec_2 (0 : Int)) (Znth i xs_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) a_pre b_pre)) (PreH4 : (rj = (0 : Int))) (PreH5 : (rj = (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (ri ≠ (0 : Int))) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : ((0 : Int) <= ri)) (PreH25 : (ri < 2)) (PreH26 : ((0 : Int) <= rj)) (PreH27 : (rj <= 2)) (PreH28 : ((0 : Int) <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best)) (PreH31 : (retval ≠ (0 : Int))) ,
  (BestBefore paper seals i j ri ((0 : Int) + 1) best)

noncomputable def solver_entail_wit_10_7 : Prop :=
  (
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : ((((Znth i xs_spec_2 (0 : Int)) * (Znth i ys_spec_2 (0 : Int))) + ((Znth j ys_spec_2 (0 : Int)) * (Znth j xs_spec_2 (0 : Int)))) <= best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i xs_spec_2 (0 : Int)) (Znth i ys_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) a_pre b_pre)) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (rj ≠ (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (ri = (0 : Int))) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : ((0 : Int) <= ri)) (PreH25 : (ri < 2)) (PreH26 : ((0 : Int) <= rj)) (PreH27 : (rj <= 2)) (PreH28 : ((0 : Int) <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best)) (PreH31 : (retval ≠ (0 : Int))) ,
  (intArray.full x_pre n_pre xs_spec_2)
  ** (intArray.full y_pre n_pre ys_spec_2)
|--
  EX ys_spec : (List Int), EX xs_spec : (List Int),
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= (rj + 1)) ” &&
  “ ((rj + 1) <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri (rj + 1) best) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
) \/
(
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : ((((Znth i xs_spec_2 (0 : Int)) * (Znth i ys_spec_2 (0 : Int))) + ((Znth j ys_spec_2 (0 : Int)) * (Znth j xs_spec_2 (0 : Int)))) <= best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i xs_spec_2 (0 : Int)) (Znth i ys_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) a_pre b_pre)) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (rj ≠ (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (ri = (0 : Int))) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : ((0 : Int) <= ri)) (PreH25 : (ri < 2)) (PreH26 : ((0 : Int) <= rj)) (PreH27 : (rj <= 2)) (PreH28 : ((0 : Int) <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best)) (PreH31 : (retval ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (BestBefore paper seals i j (0 : Int) (rj + 1) best) ”
  &&  emp
)

noncomputable def solver_entail_wit_10_7_split_goal_1 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : ((((Znth i xs_spec_2 (0 : Int)) * (Znth i ys_spec_2 (0 : Int))) + ((Znth j ys_spec_2 (0 : Int)) * (Znth j xs_spec_2 (0 : Int)))) <= best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i xs_spec_2 (0 : Int)) (Znth i ys_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) a_pre b_pre)) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (rj ≠ (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (ri = (0 : Int))) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : ((0 : Int) <= ri)) (PreH25 : (ri < 2)) (PreH26 : ((0 : Int) <= rj)) (PreH27 : (rj <= 2)) (PreH28 : ((0 : Int) <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best)) (PreH31 : (retval ≠ (0 : Int))) ,
  (BestBefore paper seals i j (0 : Int) (rj + 1) best)

noncomputable def solver_entail_wit_10_8 : Prop :=
  (
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : ((((Znth i xs_spec_2 (0 : Int)) * (Znth i ys_spec_2 (0 : Int))) + ((Znth j xs_spec_2 (0 : Int)) * (Znth j ys_spec_2 (0 : Int)))) <= best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i xs_spec_2 (0 : Int)) (Znth i ys_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) a_pre b_pre)) (PreH4 : (rj = (0 : Int))) (PreH5 : (rj = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (ri = (0 : Int))) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : ((0 : Int) <= ri)) (PreH25 : (ri < 2)) (PreH26 : ((0 : Int) <= rj)) (PreH27 : (rj <= 2)) (PreH28 : ((0 : Int) <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best)) (PreH31 : (retval ≠ (0 : Int))) ,
  (intArray.full y_pre n_pre ys_spec_2)
  ** (intArray.full x_pre n_pre xs_spec_2)
|--
  EX ys_spec : (List Int), EX xs_spec : (List Int),
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= (rj + 1)) ” &&
  “ ((rj + 1) <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri (rj + 1) best) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
) \/
(
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : ((((Znth i xs_spec_2 (0 : Int)) * (Znth i ys_spec_2 (0 : Int))) + ((Znth j xs_spec_2 (0 : Int)) * (Znth j ys_spec_2 (0 : Int)))) <= best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i xs_spec_2 (0 : Int)) (Znth i ys_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) a_pre b_pre)) (PreH4 : (rj = (0 : Int))) (PreH5 : (rj = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (ri = (0 : Int))) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : ((0 : Int) <= ri)) (PreH25 : (ri < 2)) (PreH26 : ((0 : Int) <= rj)) (PreH27 : (rj <= 2)) (PreH28 : ((0 : Int) <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best)) (PreH31 : (retval ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (BestBefore paper seals i j (0 : Int) ((0 : Int) + 1) best) ”
  &&  emp
)

noncomputable def solver_entail_wit_10_8_split_goal_1 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : ((((Znth i xs_spec_2 (0 : Int)) * (Znth i ys_spec_2 (0 : Int))) + ((Znth j xs_spec_2 (0 : Int)) * (Znth j ys_spec_2 (0 : Int)))) <= best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i xs_spec_2 (0 : Int)) (Znth i ys_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) a_pre b_pre)) (PreH4 : (rj = (0 : Int))) (PreH5 : (rj = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (ri = (0 : Int))) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : ((0 : Int) <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : ((0 : Int) <= ri)) (PreH25 : (ri < 2)) (PreH26 : ((0 : Int) <= rj)) (PreH27 : (rj <= 2)) (PreH28 : ((0 : Int) <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best)) (PreH31 : (retval ≠ (0 : Int))) ,
  (BestBefore paper seals i j (0 : Int) ((0 : Int) + 1) best)

noncomputable def solver_entail_wit_10_9 : Prop :=
  (
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = (0 : Int))) (PreH2 : ¬((FitsDims (Znth i ys_spec_2 (0 : Int)) (Znth i xs_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) a_pre b_pre))) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec_2)) = n_pre)) (PreH18 : ((Zlength (ys_spec_2)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval = (0 : Int))) ,
  (intArray.full x_pre n_pre xs_spec_2)
  ** (intArray.full y_pre n_pre ys_spec_2)
|--
  EX ys_spec : (List Int), EX xs_spec : (List Int),
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= (rj + 1)) ” &&
  “ ((rj + 1) <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri (rj + 1) best) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
) \/
(
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = (0 : Int))) (PreH2 : ¬((FitsDims (Znth i ys_spec_2 (0 : Int)) (Znth i xs_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) a_pre b_pre))) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec_2)) = n_pre)) (PreH18 : ((Zlength (ys_spec_2)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval = (0 : Int))) ,
  TT && emp 
|--
  “ (BestBefore paper seals i j ri (rj + 1) best) ”
  &&  emp
)

noncomputable def solver_entail_wit_10_9_split_goal_1 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = (0 : Int))) (PreH2 : ¬((FitsDims (Znth i ys_spec_2 (0 : Int)) (Znth i xs_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) a_pre b_pre))) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec_2)) = n_pre)) (PreH18 : ((Zlength (ys_spec_2)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval = (0 : Int))) ,
  (BestBefore paper seals i j ri (rj + 1) best)

noncomputable def solver_entail_wit_10_10 : Prop :=
  (
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = (0 : Int))) (PreH2 : ¬((FitsDims (Znth i ys_spec_2 (0 : Int)) (Znth i xs_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) a_pre b_pre))) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec_2)) = n_pre)) (PreH18 : ((Zlength (ys_spec_2)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval = (0 : Int))) ,
  (intArray.full y_pre n_pre ys_spec_2)
  ** (intArray.full x_pre n_pre xs_spec_2)
|--
  EX ys_spec : (List Int), EX xs_spec : (List Int),
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= (rj + 1)) ” &&
  “ ((rj + 1) <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri (rj + 1) best) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
) \/
(
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = (0 : Int))) (PreH2 : ¬((FitsDims (Znth i ys_spec_2 (0 : Int)) (Znth i xs_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) a_pre b_pre))) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec_2)) = n_pre)) (PreH18 : ((Zlength (ys_spec_2)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval = (0 : Int))) ,
  TT && emp 
|--
  “ (BestBefore paper seals i j ri ((0 : Int) + 1) best) ”
  &&  emp
)

noncomputable def solver_entail_wit_10_10_split_goal_1 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = (0 : Int))) (PreH2 : ¬((FitsDims (Znth i ys_spec_2 (0 : Int)) (Znth i xs_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) a_pre b_pre))) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri ≠ (0 : Int))) (PreH6 : (ri ≠ (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec_2)) = n_pre)) (PreH18 : ((Zlength (ys_spec_2)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval = (0 : Int))) ,
  (BestBefore paper seals i j ri ((0 : Int) + 1) best)

noncomputable def solver_entail_wit_10_11 : Prop :=
  (
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = (0 : Int))) (PreH2 : ¬((FitsDims (Znth i xs_spec_2 (0 : Int)) (Znth i ys_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) a_pre b_pre))) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec_2)) = n_pre)) (PreH18 : ((Zlength (ys_spec_2)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval = (0 : Int))) ,
  (intArray.full x_pre n_pre xs_spec_2)
  ** (intArray.full y_pre n_pre ys_spec_2)
|--
  EX ys_spec : (List Int), EX xs_spec : (List Int),
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= (rj + 1)) ” &&
  “ ((rj + 1) <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri (rj + 1) best) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
) \/
(
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = (0 : Int))) (PreH2 : ¬((FitsDims (Znth i xs_spec_2 (0 : Int)) (Znth i ys_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) a_pre b_pre))) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec_2)) = n_pre)) (PreH18 : ((Zlength (ys_spec_2)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval = (0 : Int))) ,
  TT && emp 
|--
  “ (BestBefore paper seals i j (0 : Int) (rj + 1) best) ”
  &&  emp
)

noncomputable def solver_entail_wit_10_11_split_goal_1 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = (0 : Int))) (PreH2 : ¬((FitsDims (Znth i xs_spec_2 (0 : Int)) (Znth i ys_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) a_pre b_pre))) (PreH3 : (rj ≠ (0 : Int))) (PreH4 : (rj ≠ (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec_2)) = n_pre)) (PreH18 : ((Zlength (ys_spec_2)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval = (0 : Int))) ,
  (BestBefore paper seals i j (0 : Int) (rj + 1) best)

noncomputable def solver_entail_wit_10_12 : Prop :=
  (
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = (0 : Int))) (PreH2 : ¬((FitsDims (Znth i xs_spec_2 (0 : Int)) (Znth i ys_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) a_pre b_pre))) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec_2)) = n_pre)) (PreH18 : ((Zlength (ys_spec_2)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval = (0 : Int))) ,
  (intArray.full y_pre n_pre ys_spec_2)
  ** (intArray.full x_pre n_pre xs_spec_2)
|--
  EX ys_spec : (List Int), EX xs_spec : (List Int),
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= (rj + 1)) ” &&
  “ ((rj + 1) <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri (rj + 1) best) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
) \/
(
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = (0 : Int))) (PreH2 : ¬((FitsDims (Znth i xs_spec_2 (0 : Int)) (Znth i ys_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) a_pre b_pre))) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec_2)) = n_pre)) (PreH18 : ((Zlength (ys_spec_2)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval = (0 : Int))) ,
  TT && emp 
|--
  “ (BestBefore paper seals i j (0 : Int) ((0 : Int) + 1) best) ”
  &&  emp
)

noncomputable def solver_entail_wit_10_12_split_goal_1 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (retval : Int) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (retval = (0 : Int))) (PreH2 : ¬((FitsDims (Znth i xs_spec_2 (0 : Int)) (Znth i ys_spec_2 (0 : Int)) (Znth j xs_spec_2 (0 : Int)) (Znth j ys_spec_2 (0 : Int)) a_pre b_pre))) (PreH3 : (rj = (0 : Int))) (PreH4 : (rj = (0 : Int))) (PreH5 : (ri = (0 : Int))) (PreH6 : (ri = (0 : Int))) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec_2)) = n_pre)) (PreH18 : ((Zlength (ys_spec_2)) = n_pre)) (PreH19 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : ((0 : Int) <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : ((0 : Int) <= ri)) (PreH24 : (ri < 2)) (PreH25 : ((0 : Int) <= rj)) (PreH26 : (rj <= 2)) (PreH27 : ((0 : Int) <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best)) (PreH30 : (retval = (0 : Int))) ,
  (BestBefore paper seals i j (0 : Int) ((0 : Int) + 1) best)

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (i_2 : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH14 : ((0 : Int) <= i_2)) (PreH15 : (i_2 <= n_pre)) (PreH16 : ((0 : Int) <= best)) (PreH17 : (best <= 20000)) (PreH18 : (BestBefore paper seals i_2 (i_2 + 1) (0 : Int) (0 : Int) best)) ,
  (intArray.full x_pre n_pre xs_spec_2)
  ** (intArray.full y_pre n_pre ys_spec_2)
|--
  EX ys_spec : (List Int), EX xs_spec : (List Int),
  “ (Spec paper seals best) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((Znth i xs_spec (0 : Int)) = (fst ((Znth i seals __default__Prod_Z_Z)))) ∧ ((Znth i ys_spec (0 : Int)) = (snd ((Znth i seals __default__Prod_Z_Z)))))) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
) \/
(
forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (i_2 : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH14 : ((0 : Int) <= i_2)) (PreH15 : (i_2 <= n_pre)) (PreH16 : ((0 : Int) <= best)) (PreH17 : (best <= 20000)) (PreH18 : (BestBefore paper seals i_2 (i_2 + 1) (0 : Int) (0 : Int) best)) ,
  TT && emp 
|--
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((Znth i xs_spec_2 (0 : Int)) = (fst ((Znth i seals __default__Prod_Z_Z)))) ∧ ((Znth i ys_spec_2 (0 : Int)) = (snd ((Znth i seals __default__Prod_Z_Z)))))) ” &&
  “ (Spec paper seals best) ”
  &&  emp
)

noncomputable def solver_return_wit_1_split_goal_1 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (i_2 : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH14 : ((0 : Int) <= i_2)) (PreH15 : (i_2 <= n_pre)) (PreH16 : ((0 : Int) <= best)) (PreH17 : (best <= 20000)) (PreH18 : (BestBefore paper seals i_2 (i_2 + 1) (0 : Int) (0 : Int) best)) ,
  forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> (((Znth i xs_spec_2 (0 : Int)) = (fst ((Znth i seals __default__Prod_Z_Z)))) ∧ ((Znth i ys_spec_2 (0 : Int)) = (snd ((Znth i seals __default__Prod_Z_Z))))))

noncomputable def solver_return_wit_1_split_goal_2 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (i_2 : Int) (ys_spec_2 : (List Int)) (xs_spec_2 : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (i_2 >= n_pre)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec_2 (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec_2 (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH14 : ((0 : Int) <= i_2)) (PreH15 : (i_2 <= n_pre)) (PreH16 : ((0 : Int) <= best)) (PreH17 : (best <= 20000)) (PreH18 : (BestBefore paper seals i_2 (i_2 + 1) (0 : Int) (0 : Int) best)) ,
  (Spec paper seals best)

noncomputable def solver_partial_solve_wit_1 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (ri ≠ (0 : Int))) (PreH2 : (ri ≠ (0 : Int))) (PreH3 : (rj < 2)) (PreH4 : (1 <= (fst (paper)))) (PreH5 : ((fst (paper)) <= 100)) (PreH6 : (1 <= (snd (paper)))) (PreH7 : ((snd (paper)) <= 100)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((fst (paper)) = a_pre)) (PreH11 : ((snd (paper)) = b_pre)) (PreH12 : (n_pre = (Zlength (seals)))) (PreH13 : ((Zlength (xs_spec)) = n_pre)) (PreH14 : ((Zlength (ys_spec)) = n_pre)) (PreH15 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < j)) (PreH18 : (j < n_pre)) (PreH19 : ((0 : Int) <= ri)) (PreH20 : (ri < 2)) (PreH21 : ((0 : Int) <= rj)) (PreH22 : (rj <= 2)) (PreH23 : ((0 : Int) <= best)) (PreH24 : (best <= 20000)) (PreH25 : (BestBefore paper seals i j ri rj best)) ,
  (intArray.full y_pre n_pre ys_spec)
  ** (intArray.full x_pre n_pre xs_spec)
|--
  “ (ri ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ”
  &&  (((x_pre + (i * sizeof(INT)))) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** (intArray.missing_i x_pre i (0 : Int) n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)

noncomputable def solver_partial_solve_wit_2 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (ri = (0 : Int))) (PreH2 : (ri = (0 : Int))) (PreH3 : (rj < 2)) (PreH4 : (1 <= (fst (paper)))) (PreH5 : ((fst (paper)) <= 100)) (PreH6 : (1 <= (snd (paper)))) (PreH7 : ((snd (paper)) <= 100)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((fst (paper)) = a_pre)) (PreH11 : ((snd (paper)) = b_pre)) (PreH12 : (n_pre = (Zlength (seals)))) (PreH13 : ((Zlength (xs_spec)) = n_pre)) (PreH14 : ((Zlength (ys_spec)) = n_pre)) (PreH15 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < j)) (PreH18 : (j < n_pre)) (PreH19 : ((0 : Int) <= ri)) (PreH20 : (ri < 2)) (PreH21 : ((0 : Int) <= rj)) (PreH22 : (rj <= 2)) (PreH23 : ((0 : Int) <= best)) (PreH24 : (best <= 20000)) (PreH25 : (BestBefore paper seals i j ri rj best)) ,
  (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
|--
  “ (ri = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ”
  &&  (((y_pre + (i * sizeof(INT)))) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** (intArray.missing_i y_pre i (0 : Int) n_pre ys_spec)
  ** (intArray.full x_pre n_pre xs_spec)

noncomputable def solver_partial_solve_wit_3 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (ri ≠ (0 : Int))) (PreH2 : (rj < 2)) (PreH3 : (1 <= (fst (paper)))) (PreH4 : ((fst (paper)) <= 100)) (PreH5 : (1 <= (snd (paper)))) (PreH6 : ((snd (paper)) <= 100)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : ((fst (paper)) = a_pre)) (PreH10 : ((snd (paper)) = b_pre)) (PreH11 : (n_pre = (Zlength (seals)))) (PreH12 : ((Zlength (xs_spec)) = n_pre)) (PreH13 : ((Zlength (ys_spec)) = n_pre)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i < j)) (PreH17 : (j < n_pre)) (PreH18 : ((0 : Int) <= ri)) (PreH19 : (ri < 2)) (PreH20 : ((0 : Int) <= rj)) (PreH21 : (rj <= 2)) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 20000)) (PreH24 : (BestBefore paper seals i j ri rj best)) ,
  (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
|--
  “ (ri ≠ (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ”
  &&  (((y_pre + (i * sizeof(INT)))) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** (intArray.missing_i y_pre i (0 : Int) n_pre ys_spec)
  ** (intArray.full x_pre n_pre xs_spec)

noncomputable def solver_partial_solve_wit_4 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (ri = (0 : Int))) (PreH2 : (rj < 2)) (PreH3 : (1 <= (fst (paper)))) (PreH4 : ((fst (paper)) <= 100)) (PreH5 : (1 <= (snd (paper)))) (PreH6 : ((snd (paper)) <= 100)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : ((fst (paper)) = a_pre)) (PreH10 : ((snd (paper)) = b_pre)) (PreH11 : (n_pre = (Zlength (seals)))) (PreH12 : ((Zlength (xs_spec)) = n_pre)) (PreH13 : ((Zlength (ys_spec)) = n_pre)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i < j)) (PreH17 : (j < n_pre)) (PreH18 : ((0 : Int) <= ri)) (PreH19 : (ri < 2)) (PreH20 : ((0 : Int) <= rj)) (PreH21 : (rj <= 2)) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 20000)) (PreH24 : (BestBefore paper seals i j ri rj best)) ,
  (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
|--
  “ (ri = (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ”
  &&  (((x_pre + (i * sizeof(INT)))) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** (intArray.missing_i x_pre i (0 : Int) n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)

noncomputable def solver_partial_solve_wit_5 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (rj ≠ (0 : Int))) (PreH2 : (rj ≠ (0 : Int))) (PreH3 : (ri ≠ (0 : Int))) (PreH4 : (ri ≠ (0 : Int))) (PreH5 : (rj < 2)) (PreH6 : (1 <= (fst (paper)))) (PreH7 : ((fst (paper)) <= 100)) (PreH8 : (1 <= (snd (paper)))) (PreH9 : ((snd (paper)) <= 100)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : ((fst (paper)) = a_pre)) (PreH13 : ((snd (paper)) = b_pre)) (PreH14 : (n_pre = (Zlength (seals)))) (PreH15 : ((Zlength (xs_spec)) = n_pre)) (PreH16 : ((Zlength (ys_spec)) = n_pre)) (PreH17 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i < j)) (PreH20 : (j < n_pre)) (PreH21 : ((0 : Int) <= ri)) (PreH22 : (ri < 2)) (PreH23 : ((0 : Int) <= rj)) (PreH24 : (rj <= 2)) (PreH25 : ((0 : Int) <= best)) (PreH26 : (best <= 20000)) (PreH27 : (BestBefore paper seals i j ri rj best)) ,
  (intArray.full y_pre n_pre ys_spec)
  ** (intArray.full x_pre n_pre xs_spec)
|--
  “ (rj ≠ (0 : Int)) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ”
  &&  (((x_pre + (j * sizeof(INT)))) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.missing_i x_pre j (0 : Int) n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)

noncomputable def solver_partial_solve_wit_6 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (rj = (0 : Int))) (PreH2 : (rj = (0 : Int))) (PreH3 : (ri ≠ (0 : Int))) (PreH4 : (ri ≠ (0 : Int))) (PreH5 : (rj < 2)) (PreH6 : (1 <= (fst (paper)))) (PreH7 : ((fst (paper)) <= 100)) (PreH8 : (1 <= (snd (paper)))) (PreH9 : ((snd (paper)) <= 100)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : ((fst (paper)) = a_pre)) (PreH13 : ((snd (paper)) = b_pre)) (PreH14 : (n_pre = (Zlength (seals)))) (PreH15 : ((Zlength (xs_spec)) = n_pre)) (PreH16 : ((Zlength (ys_spec)) = n_pre)) (PreH17 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i < j)) (PreH20 : (j < n_pre)) (PreH21 : ((0 : Int) <= ri)) (PreH22 : (ri < 2)) (PreH23 : ((0 : Int) <= rj)) (PreH24 : (rj <= 2)) (PreH25 : ((0 : Int) <= best)) (PreH26 : (best <= 20000)) (PreH27 : (BestBefore paper seals i j ri rj best)) ,
  (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
|--
  “ (rj = (0 : Int)) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ”
  &&  (((y_pre + (j * sizeof(INT)))) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.missing_i y_pre j (0 : Int) n_pre ys_spec)
  ** (intArray.full x_pre n_pre xs_spec)

noncomputable def solver_partial_solve_wit_7 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (rj ≠ (0 : Int))) (PreH2 : (rj ≠ (0 : Int))) (PreH3 : (ri = (0 : Int))) (PreH4 : (ri = (0 : Int))) (PreH5 : (rj < 2)) (PreH6 : (1 <= (fst (paper)))) (PreH7 : ((fst (paper)) <= 100)) (PreH8 : (1 <= (snd (paper)))) (PreH9 : ((snd (paper)) <= 100)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : ((fst (paper)) = a_pre)) (PreH13 : ((snd (paper)) = b_pre)) (PreH14 : (n_pre = (Zlength (seals)))) (PreH15 : ((Zlength (xs_spec)) = n_pre)) (PreH16 : ((Zlength (ys_spec)) = n_pre)) (PreH17 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i < j)) (PreH20 : (j < n_pre)) (PreH21 : ((0 : Int) <= ri)) (PreH22 : (ri < 2)) (PreH23 : ((0 : Int) <= rj)) (PreH24 : (rj <= 2)) (PreH25 : ((0 : Int) <= best)) (PreH26 : (best <= 20000)) (PreH27 : (BestBefore paper seals i j ri rj best)) ,
  (intArray.full y_pre n_pre ys_spec)
  ** (intArray.full x_pre n_pre xs_spec)
|--
  “ (rj ≠ (0 : Int)) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ”
  &&  (((x_pre + (j * sizeof(INT)))) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.missing_i x_pre j (0 : Int) n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)

noncomputable def solver_partial_solve_wit_8 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (rj = (0 : Int))) (PreH2 : (rj = (0 : Int))) (PreH3 : (ri = (0 : Int))) (PreH4 : (ri = (0 : Int))) (PreH5 : (rj < 2)) (PreH6 : (1 <= (fst (paper)))) (PreH7 : ((fst (paper)) <= 100)) (PreH8 : (1 <= (snd (paper)))) (PreH9 : ((snd (paper)) <= 100)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : ((fst (paper)) = a_pre)) (PreH13 : ((snd (paper)) = b_pre)) (PreH14 : (n_pre = (Zlength (seals)))) (PreH15 : ((Zlength (xs_spec)) = n_pre)) (PreH16 : ((Zlength (ys_spec)) = n_pre)) (PreH17 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i < j)) (PreH20 : (j < n_pre)) (PreH21 : ((0 : Int) <= ri)) (PreH22 : (ri < 2)) (PreH23 : ((0 : Int) <= rj)) (PreH24 : (rj <= 2)) (PreH25 : ((0 : Int) <= best)) (PreH26 : (best <= 20000)) (PreH27 : (BestBefore paper seals i j ri rj best)) ,
  (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
|--
  “ (rj = (0 : Int)) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ”
  &&  (((y_pre + (j * sizeof(INT)))) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.missing_i y_pre j (0 : Int) n_pre ys_spec)
  ** (intArray.full x_pre n_pre xs_spec)

noncomputable def solver_partial_solve_wit_9 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (rj ≠ (0 : Int))) (PreH2 : (ri ≠ (0 : Int))) (PreH3 : (ri ≠ (0 : Int))) (PreH4 : (rj < 2)) (PreH5 : (1 <= (fst (paper)))) (PreH6 : ((fst (paper)) <= 100)) (PreH7 : (1 <= (snd (paper)))) (PreH8 : ((snd (paper)) <= 100)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : ((fst (paper)) = a_pre)) (PreH12 : ((snd (paper)) = b_pre)) (PreH13 : (n_pre = (Zlength (seals)))) (PreH14 : ((Zlength (xs_spec)) = n_pre)) (PreH15 : ((Zlength (ys_spec)) = n_pre)) (PreH16 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < j)) (PreH19 : (j < n_pre)) (PreH20 : ((0 : Int) <= ri)) (PreH21 : (ri < 2)) (PreH22 : ((0 : Int) <= rj)) (PreH23 : (rj <= 2)) (PreH24 : ((0 : Int) <= best)) (PreH25 : (best <= 20000)) (PreH26 : (BestBefore paper seals i j ri rj best)) ,
  (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
|--
  “ (rj ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ”
  &&  (((y_pre + (j * sizeof(INT)))) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.missing_i y_pre j (0 : Int) n_pre ys_spec)
  ** (intArray.full x_pre n_pre xs_spec)

noncomputable def solver_partial_solve_wit_10 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (rj = (0 : Int))) (PreH2 : (ri ≠ (0 : Int))) (PreH3 : (ri ≠ (0 : Int))) (PreH4 : (rj < 2)) (PreH5 : (1 <= (fst (paper)))) (PreH6 : ((fst (paper)) <= 100)) (PreH7 : (1 <= (snd (paper)))) (PreH8 : ((snd (paper)) <= 100)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : ((fst (paper)) = a_pre)) (PreH12 : ((snd (paper)) = b_pre)) (PreH13 : (n_pre = (Zlength (seals)))) (PreH14 : ((Zlength (xs_spec)) = n_pre)) (PreH15 : ((Zlength (ys_spec)) = n_pre)) (PreH16 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < j)) (PreH19 : (j < n_pre)) (PreH20 : ((0 : Int) <= ri)) (PreH21 : (ri < 2)) (PreH22 : ((0 : Int) <= rj)) (PreH23 : (rj <= 2)) (PreH24 : ((0 : Int) <= best)) (PreH25 : (best <= 20000)) (PreH26 : (BestBefore paper seals i j ri rj best)) ,
  (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
|--
  “ (rj = (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ”
  &&  (((x_pre + (j * sizeof(INT)))) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.missing_i x_pre j (0 : Int) n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)

noncomputable def solver_partial_solve_wit_11 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (rj ≠ (0 : Int))) (PreH2 : (ri = (0 : Int))) (PreH3 : (ri = (0 : Int))) (PreH4 : (rj < 2)) (PreH5 : (1 <= (fst (paper)))) (PreH6 : ((fst (paper)) <= 100)) (PreH7 : (1 <= (snd (paper)))) (PreH8 : ((snd (paper)) <= 100)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : ((fst (paper)) = a_pre)) (PreH12 : ((snd (paper)) = b_pre)) (PreH13 : (n_pre = (Zlength (seals)))) (PreH14 : ((Zlength (xs_spec)) = n_pre)) (PreH15 : ((Zlength (ys_spec)) = n_pre)) (PreH16 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < j)) (PreH19 : (j < n_pre)) (PreH20 : ((0 : Int) <= ri)) (PreH21 : (ri < 2)) (PreH22 : ((0 : Int) <= rj)) (PreH23 : (rj <= 2)) (PreH24 : ((0 : Int) <= best)) (PreH25 : (best <= 20000)) (PreH26 : (BestBefore paper seals i j ri rj best)) ,
  (intArray.full y_pre n_pre ys_spec)
  ** (intArray.full x_pre n_pre xs_spec)
|--
  “ (rj ≠ (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ”
  &&  (((y_pre + (j * sizeof(INT)))) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.missing_i y_pre j (0 : Int) n_pre ys_spec)
  ** (intArray.full x_pre n_pre xs_spec)

noncomputable def solver_partial_solve_wit_12 : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (rj = (0 : Int))) (PreH2 : (ri = (0 : Int))) (PreH3 : (ri = (0 : Int))) (PreH4 : (rj < 2)) (PreH5 : (1 <= (fst (paper)))) (PreH6 : ((fst (paper)) <= 100)) (PreH7 : (1 <= (snd (paper)))) (PreH8 : ((snd (paper)) <= 100)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : ((fst (paper)) = a_pre)) (PreH12 : ((snd (paper)) = b_pre)) (PreH13 : (n_pre = (Zlength (seals)))) (PreH14 : ((Zlength (xs_spec)) = n_pre)) (PreH15 : ((Zlength (ys_spec)) = n_pre)) (PreH16 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < j)) (PreH19 : (j < n_pre)) (PreH20 : ((0 : Int) <= ri)) (PreH21 : (ri < 2)) (PreH22 : ((0 : Int) <= rj)) (PreH23 : (rj <= 2)) (PreH24 : ((0 : Int) <= best)) (PreH25 : (best <= 20000)) (PreH26 : (BestBefore paper seals i j ri rj best)) ,
  (intArray.full y_pre n_pre ys_spec)
  ** (intArray.full x_pre n_pre xs_spec)
|--
  “ (rj = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ”
  &&  (((x_pre + (j * sizeof(INT)))) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.missing_i x_pre j (0 : Int) n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)

noncomputable def solver_partial_solve_wit_13_pure : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (rj ≠ (0 : Int))) (PreH2 : (rj ≠ (0 : Int))) (PreH3 : (ri ≠ (0 : Int))) (PreH4 : (ri ≠ (0 : Int))) (PreH5 : (rj < 2)) (PreH6 : (1 <= (fst (paper)))) (PreH7 : ((fst (paper)) <= 100)) (PreH8 : (1 <= (snd (paper)))) (PreH9 : ((snd (paper)) <= 100)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : ((fst (paper)) = a_pre)) (PreH13 : ((snd (paper)) = b_pre)) (PreH14 : (n_pre = (Zlength (seals)))) (PreH15 : ((Zlength (xs_spec)) = n_pre)) (PreH16 : ((Zlength (ys_spec)) = n_pre)) (PreH17 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i < j)) (PreH20 : (j < n_pre)) (PreH21 : ((0 : Int) <= ri)) (PreH22 : (ri < 2)) (PreH23 : ((0 : Int) <= rj)) (PreH24 : (rj <= 2)) (PreH25 : ((0 : Int) <= best)) (PreH26 : (best <= 20000)) (PreH27 : (BestBefore paper seals i j ri rj best)) ,
  (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ (1 <= (Znth i ys_spec (0 : Int))) ” &&
  “ ((Znth i ys_spec (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth i xs_spec (0 : Int))) ” &&
  “ ((Znth i xs_spec (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth j ys_spec (0 : Int))) ” &&
  “ ((Znth j ys_spec (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth j xs_spec (0 : Int))) ” &&
  “ ((Znth j xs_spec (0 : Int)) <= 100) ” &&
  “ (1 <= a_pre) ” &&
  “ (a_pre <= 100) ” &&
  “ (1 <= b_pre) ” &&
  “ (b_pre <= 100) ”

noncomputable def solver_partial_solve_wit_13_aux : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (rj ≠ (0 : Int))) (PreH2 : (rj ≠ (0 : Int))) (PreH3 : (ri ≠ (0 : Int))) (PreH4 : (ri ≠ (0 : Int))) (PreH5 : (rj < 2)) (PreH6 : (1 <= (fst (paper)))) (PreH7 : ((fst (paper)) <= 100)) (PreH8 : (1 <= (snd (paper)))) (PreH9 : ((snd (paper)) <= 100)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : ((fst (paper)) = a_pre)) (PreH13 : ((snd (paper)) = b_pre)) (PreH14 : (n_pre = (Zlength (seals)))) (PreH15 : ((Zlength (xs_spec)) = n_pre)) (PreH16 : ((Zlength (ys_spec)) = n_pre)) (PreH17 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i < j)) (PreH20 : (j < n_pre)) (PreH21 : ((0 : Int) <= ri)) (PreH22 : (ri < 2)) (PreH23 : ((0 : Int) <= rj)) (PreH24 : (rj <= 2)) (PreH25 : ((0 : Int) <= best)) (PreH26 : (best <= 20000)) (PreH27 : (BestBefore paper seals i j ri rj best)) ,
  (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
|--
  “ (1 <= (Znth i ys_spec (0 : Int))) ” &&
  “ ((Znth i ys_spec (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth i xs_spec (0 : Int))) ” &&
  “ ((Znth i xs_spec (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth j ys_spec (0 : Int))) ” &&
  “ ((Znth j ys_spec (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth j xs_spec (0 : Int))) ” &&
  “ ((Znth j xs_spec (0 : Int)) <= 100) ” &&
  “ (1 <= a_pre) ” &&
  “ (a_pre <= 100) ” &&
  “ (1 <= b_pre) ” &&
  “ (b_pre <= 100) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)

noncomputable def solver_partial_solve_wit_13 : Prop := solver_partial_solve_wit_13_pure -> solver_partial_solve_wit_13_aux

noncomputable def solver_partial_solve_wit_14_pure : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (rj = (0 : Int))) (PreH2 : (rj = (0 : Int))) (PreH3 : (ri ≠ (0 : Int))) (PreH4 : (ri ≠ (0 : Int))) (PreH5 : (rj < 2)) (PreH6 : (1 <= (fst (paper)))) (PreH7 : ((fst (paper)) <= 100)) (PreH8 : (1 <= (snd (paper)))) (PreH9 : ((snd (paper)) <= 100)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : ((fst (paper)) = a_pre)) (PreH13 : ((snd (paper)) = b_pre)) (PreH14 : (n_pre = (Zlength (seals)))) (PreH15 : ((Zlength (xs_spec)) = n_pre)) (PreH16 : ((Zlength (ys_spec)) = n_pre)) (PreH17 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i < j)) (PreH20 : (j < n_pre)) (PreH21 : ((0 : Int) <= ri)) (PreH22 : (ri < 2)) (PreH23 : ((0 : Int) <= rj)) (PreH24 : (rj <= 2)) (PreH25 : ((0 : Int) <= best)) (PreH26 : (best <= 20000)) (PreH27 : (BestBefore paper seals i j ri rj best)) ,
  (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ (1 <= (Znth i ys_spec (0 : Int))) ” &&
  “ ((Znth i ys_spec (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth i xs_spec (0 : Int))) ” &&
  “ ((Znth i xs_spec (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth j xs_spec (0 : Int))) ” &&
  “ ((Znth j xs_spec (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth j ys_spec (0 : Int))) ” &&
  “ ((Znth j ys_spec (0 : Int)) <= 100) ” &&
  “ (1 <= a_pre) ” &&
  “ (a_pre <= 100) ” &&
  “ (1 <= b_pre) ” &&
  “ (b_pre <= 100) ”

noncomputable def solver_partial_solve_wit_14_aux : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (rj = (0 : Int))) (PreH2 : (rj = (0 : Int))) (PreH3 : (ri ≠ (0 : Int))) (PreH4 : (ri ≠ (0 : Int))) (PreH5 : (rj < 2)) (PreH6 : (1 <= (fst (paper)))) (PreH7 : ((fst (paper)) <= 100)) (PreH8 : (1 <= (snd (paper)))) (PreH9 : ((snd (paper)) <= 100)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : ((fst (paper)) = a_pre)) (PreH13 : ((snd (paper)) = b_pre)) (PreH14 : (n_pre = (Zlength (seals)))) (PreH15 : ((Zlength (xs_spec)) = n_pre)) (PreH16 : ((Zlength (ys_spec)) = n_pre)) (PreH17 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i < j)) (PreH20 : (j < n_pre)) (PreH21 : ((0 : Int) <= ri)) (PreH22 : (ri < 2)) (PreH23 : ((0 : Int) <= rj)) (PreH24 : (rj <= 2)) (PreH25 : ((0 : Int) <= best)) (PreH26 : (best <= 20000)) (PreH27 : (BestBefore paper seals i j ri rj best)) ,
  (intArray.full y_pre n_pre ys_spec)
  ** (intArray.full x_pre n_pre xs_spec)
|--
  “ (1 <= (Znth i ys_spec (0 : Int))) ” &&
  “ ((Znth i ys_spec (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth i xs_spec (0 : Int))) ” &&
  “ ((Znth i xs_spec (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth j xs_spec (0 : Int))) ” &&
  “ ((Znth j xs_spec (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth j ys_spec (0 : Int))) ” &&
  “ ((Znth j ys_spec (0 : Int)) <= 100) ” &&
  “ (1 <= a_pre) ” &&
  “ (a_pre <= 100) ” &&
  “ (1 <= b_pre) ” &&
  “ (b_pre <= 100) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (ri ≠ (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ”
  &&  (intArray.full y_pre n_pre ys_spec)
  ** (intArray.full x_pre n_pre xs_spec)

noncomputable def solver_partial_solve_wit_14 : Prop := solver_partial_solve_wit_14_pure -> solver_partial_solve_wit_14_aux

noncomputable def solver_partial_solve_wit_15_pure : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (rj ≠ (0 : Int))) (PreH2 : (rj ≠ (0 : Int))) (PreH3 : (ri = (0 : Int))) (PreH4 : (ri = (0 : Int))) (PreH5 : (rj < 2)) (PreH6 : (1 <= (fst (paper)))) (PreH7 : ((fst (paper)) <= 100)) (PreH8 : (1 <= (snd (paper)))) (PreH9 : ((snd (paper)) <= 100)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : ((fst (paper)) = a_pre)) (PreH13 : ((snd (paper)) = b_pre)) (PreH14 : (n_pre = (Zlength (seals)))) (PreH15 : ((Zlength (xs_spec)) = n_pre)) (PreH16 : ((Zlength (ys_spec)) = n_pre)) (PreH17 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i < j)) (PreH20 : (j < n_pre)) (PreH21 : ((0 : Int) <= ri)) (PreH22 : (ri < 2)) (PreH23 : ((0 : Int) <= rj)) (PreH24 : (rj <= 2)) (PreH25 : ((0 : Int) <= best)) (PreH26 : (best <= 20000)) (PreH27 : (BestBefore paper seals i j ri rj best)) ,
  (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ (1 <= (Znth i xs_spec (0 : Int))) ” &&
  “ ((Znth i xs_spec (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth i ys_spec (0 : Int))) ” &&
  “ ((Znth i ys_spec (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth j ys_spec (0 : Int))) ” &&
  “ ((Znth j ys_spec (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth j xs_spec (0 : Int))) ” &&
  “ ((Znth j xs_spec (0 : Int)) <= 100) ” &&
  “ (1 <= a_pre) ” &&
  “ (a_pre <= 100) ” &&
  “ (1 <= b_pre) ” &&
  “ (b_pre <= 100) ”

noncomputable def solver_partial_solve_wit_15_aux : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (rj ≠ (0 : Int))) (PreH2 : (rj ≠ (0 : Int))) (PreH3 : (ri = (0 : Int))) (PreH4 : (ri = (0 : Int))) (PreH5 : (rj < 2)) (PreH6 : (1 <= (fst (paper)))) (PreH7 : ((fst (paper)) <= 100)) (PreH8 : (1 <= (snd (paper)))) (PreH9 : ((snd (paper)) <= 100)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : ((fst (paper)) = a_pre)) (PreH13 : ((snd (paper)) = b_pre)) (PreH14 : (n_pre = (Zlength (seals)))) (PreH15 : ((Zlength (xs_spec)) = n_pre)) (PreH16 : ((Zlength (ys_spec)) = n_pre)) (PreH17 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i < j)) (PreH20 : (j < n_pre)) (PreH21 : ((0 : Int) <= ri)) (PreH22 : (ri < 2)) (PreH23 : ((0 : Int) <= rj)) (PreH24 : (rj <= 2)) (PreH25 : ((0 : Int) <= best)) (PreH26 : (best <= 20000)) (PreH27 : (BestBefore paper seals i j ri rj best)) ,
  (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)
|--
  “ (1 <= (Znth i xs_spec (0 : Int))) ” &&
  “ ((Znth i xs_spec (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth i ys_spec (0 : Int))) ” &&
  “ ((Znth i ys_spec (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth j ys_spec (0 : Int))) ” &&
  “ ((Znth j ys_spec (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth j xs_spec (0 : Int))) ” &&
  “ ((Znth j xs_spec (0 : Int)) <= 100) ” &&
  “ (1 <= a_pre) ” &&
  “ (a_pre <= 100) ” &&
  “ (1 <= b_pre) ” &&
  “ (b_pre <= 100) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (rj ≠ (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ”
  &&  (intArray.full x_pre n_pre xs_spec)
  ** (intArray.full y_pre n_pre ys_spec)

noncomputable def solver_partial_solve_wit_15 : Prop := solver_partial_solve_wit_15_pure -> solver_partial_solve_wit_15_aux

noncomputable def solver_partial_solve_wit_16_pure : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (rj = (0 : Int))) (PreH2 : (rj = (0 : Int))) (PreH3 : (ri = (0 : Int))) (PreH4 : (ri = (0 : Int))) (PreH5 : (rj < 2)) (PreH6 : (1 <= (fst (paper)))) (PreH7 : ((fst (paper)) <= 100)) (PreH8 : (1 <= (snd (paper)))) (PreH9 : ((snd (paper)) <= 100)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : ((fst (paper)) = a_pre)) (PreH13 : ((snd (paper)) = b_pre)) (PreH14 : (n_pre = (Zlength (seals)))) (PreH15 : ((Zlength (xs_spec)) = n_pre)) (PreH16 : ((Zlength (ys_spec)) = n_pre)) (PreH17 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i < j)) (PreH20 : (j < n_pre)) (PreH21 : ((0 : Int) <= ri)) (PreH22 : (ri < 2)) (PreH23 : ((0 : Int) <= rj)) (PreH24 : (rj <= 2)) (PreH25 : ((0 : Int) <= best)) (PreH26 : (best <= 20000)) (PreH27 : (BestBefore paper seals i j ri rj best)) ,
  (intArray.full y_pre n_pre ys_spec)
  ** ((( &( "h2" ) )) # Int |-> ((Znth j ys_spec (0 : Int))))
  ** (intArray.full x_pre n_pre xs_spec)
  ** ((( &( "w2" ) )) # Int |-> ((Znth j xs_spec (0 : Int))))
  ** ((( &( "h1" ) )) # Int |-> ((Znth i ys_spec (0 : Int))))
  ** ((( &( "w1" ) )) # Int |-> ((Znth i xs_spec (0 : Int))))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Int |-> (a_pre))
  ** ((( &( "b" ) )) # Int |-> (b_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ri" ) )) # Int |-> (ri))
  ** ((( &( "rj" ) )) # Int |-> (rj))
  ** ((( &( "best" ) )) # Int |-> (best))
|--
  “ (1 <= (Znth i xs_spec (0 : Int))) ” &&
  “ ((Znth i xs_spec (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth i ys_spec (0 : Int))) ” &&
  “ ((Znth i ys_spec (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth j xs_spec (0 : Int))) ” &&
  “ ((Znth j xs_spec (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth j ys_spec (0 : Int))) ” &&
  “ ((Znth j ys_spec (0 : Int)) <= 100) ” &&
  “ (1 <= a_pre) ” &&
  “ (a_pre <= 100) ” &&
  “ (1 <= b_pre) ” &&
  “ (b_pre <= 100) ”

noncomputable def solver_partial_solve_wit_16_aux : Prop :=
  forall (seals : (List (Int × Int))) (paper : (Int × Int)) (x_pre : Int) (y_pre : Int) (n_pre : Int) (a_pre : Int) (b_pre : Int) (best : Int) (rj : Int) (ri : Int) (j : Int) (i : Int) (ys_spec : (List Int)) (xs_spec : (List Int)) (__default__Prod_Z_Z : _Prod_Z_Z) (PreH1 : (rj = (0 : Int))) (PreH2 : (rj = (0 : Int))) (PreH3 : (ri = (0 : Int))) (PreH4 : (ri = (0 : Int))) (PreH5 : (rj < 2)) (PreH6 : (1 <= (fst (paper)))) (PreH7 : ((fst (paper)) <= 100)) (PreH8 : (1 <= (snd (paper)))) (PreH9 : ((snd (paper)) <= 100)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : ((fst (paper)) = a_pre)) (PreH13 : ((snd (paper)) = b_pre)) (PreH14 : (n_pre = (Zlength (seals)))) (PreH15 : ((Zlength (xs_spec)) = n_pre)) (PreH16 : ((Zlength (ys_spec)) = n_pre)) (PreH17 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i < j)) (PreH20 : (j < n_pre)) (PreH21 : ((0 : Int) <= ri)) (PreH22 : (ri < 2)) (PreH23 : ((0 : Int) <= rj)) (PreH24 : (rj <= 2)) (PreH25 : ((0 : Int) <= best)) (PreH26 : (best <= 20000)) (PreH27 : (BestBefore paper seals i j ri rj best)) ,
  (intArray.full y_pre n_pre ys_spec)
  ** (intArray.full x_pre n_pre xs_spec)
|--
  “ (1 <= (Znth i xs_spec (0 : Int))) ” &&
  “ ((Znth i xs_spec (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth i ys_spec (0 : Int))) ” &&
  “ ((Znth i ys_spec (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth j xs_spec (0 : Int))) ” &&
  “ ((Znth j xs_spec (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth j ys_spec (0 : Int))) ” &&
  “ ((Znth j ys_spec (0 : Int)) <= 100) ” &&
  “ (1 <= a_pre) ” &&
  “ (a_pre <= 100) ” &&
  “ (1 <= b_pre) ” &&
  “ (b_pre <= 100) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (rj = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (ri = (0 : Int)) ” &&
  “ (rj < 2) ” &&
  “ (1 <= (fst (paper))) ” &&
  “ ((fst (paper)) <= 100) ” &&
  “ (1 <= (snd (paper))) ” &&
  “ ((snd (paper)) <= 100) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ ((fst (paper)) = a_pre) ” &&
  “ ((snd (paper)) = b_pre) ” &&
  “ (n_pre = (Zlength (seals))) ” &&
  “ ((Zlength (xs_spec)) = n_pre) ” &&
  “ ((Zlength (ys_spec)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) ∧ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) ∧ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) ∧ ((Znth k xs_spec (0 : Int)) = (fst ((Znth k seals __default__Prod_Z_Z))))) ∧ ((Znth k ys_spec (0 : Int)) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= ri) ” &&
  “ (ri < 2) ” &&
  “ ((0 : Int) <= rj) ” &&
  “ (rj <= 2) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 20000) ” &&
  “ (BestBefore paper seals i j ri rj best) ”
  &&  (intArray.full y_pre n_pre ys_spec)
  ** (intArray.full x_pre n_pre xs_spec)

noncomputable def solver_partial_solve_wit_16 : Prop := solver_partial_solve_wit_16_pure -> solver_partial_solve_wit_16_aux


structure VC_Correct : Type where
  proof_of_fits_safety_wit_1 : fits_safety_wit_1
  proof_of_fits_safety_wit_2 : fits_safety_wit_2
  proof_of_fits_safety_wit_3 : fits_safety_wit_3
  proof_of_fits_safety_wit_4 : fits_safety_wit_4
  proof_of_fits_safety_wit_5 : fits_safety_wit_5
  proof_of_fits_safety_wit_6 : fits_safety_wit_6
  proof_of_fits_safety_wit_7 : fits_safety_wit_7
  proof_of_fits_safety_wit_8 : fits_safety_wit_8
  proof_of_fits_safety_wit_9 : fits_safety_wit_9
  proof_of_fits_safety_wit_10 : fits_safety_wit_10
  proof_of_fits_safety_wit_11 : fits_safety_wit_11
  proof_of_fits_safety_wit_12 : fits_safety_wit_12
  proof_of_fits_safety_wit_13 : fits_safety_wit_13
  proof_of_fits_safety_wit_14 : fits_safety_wit_14
  proof_of_fits_safety_wit_15 : fits_safety_wit_15
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
  proof_of_solver_safety_wit_45 : solver_safety_wit_45
  proof_of_solver_safety_wit_46 : solver_safety_wit_46
  proof_of_solver_safety_wit_47 : solver_safety_wit_47
  proof_of_solver_safety_wit_48 : solver_safety_wit_48
  proof_of_solver_safety_wit_49 : solver_safety_wit_49
  proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1
  proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2
  proof_of_solver_entail_wit_5_3 : solver_entail_wit_5_3
  proof_of_solver_entail_wit_5_4 : solver_entail_wit_5_4
  proof_of_solver_entail_wit_5_5 : solver_entail_wit_5_5
  proof_of_solver_entail_wit_5_6 : solver_entail_wit_5_6
  proof_of_solver_entail_wit_5_7 : solver_entail_wit_5_7
  proof_of_solver_entail_wit_5_8 : solver_entail_wit_5_8
  proof_of_solver_entail_wit_6_1 : solver_entail_wit_6_1
  proof_of_solver_entail_wit_6_2 : solver_entail_wit_6_2
  proof_of_solver_entail_wit_6_3 : solver_entail_wit_6_3
  proof_of_solver_entail_wit_6_4 : solver_entail_wit_6_4
  proof_of_solver_entail_wit_6_5 : solver_entail_wit_6_5
  proof_of_solver_entail_wit_6_6 : solver_entail_wit_6_6
  proof_of_solver_entail_wit_6_7 : solver_entail_wit_6_7
  proof_of_solver_entail_wit_6_8 : solver_entail_wit_6_8
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
  proof_of_solver_partial_solve_wit_13_pure : solver_partial_solve_wit_13_pure
  proof_of_solver_partial_solve_wit_13 : solver_partial_solve_wit_13
  proof_of_solver_partial_solve_wit_14_pure : solver_partial_solve_wit_14_pure
  proof_of_solver_partial_solve_wit_14 : solver_partial_solve_wit_14
  proof_of_solver_partial_solve_wit_15_pure : solver_partial_solve_wit_15_pure
  proof_of_solver_partial_solve_wit_15 : solver_partial_solve_wit_15
  proof_of_solver_partial_solve_wit_16_pure : solver_partial_solve_wit_16_pure
  proof_of_solver_partial_solve_wit_16 : solver_partial_solve_wit_16
  proof_of_fits_return_wit_1 : fits_return_wit_1
  proof_of_fits_return_wit_2 : fits_return_wit_2
  proof_of_fits_return_wit_3 : fits_return_wit_3
  proof_of_fits_return_wit_4 : fits_return_wit_4
  proof_of_fits_return_wit_5 : fits_return_wit_5
  proof_of_fits_return_wit_6 : fits_return_wit_6
  proof_of_fits_return_wit_7 : fits_return_wit_7
  proof_of_fits_return_wit_8 : fits_return_wit_8
  proof_of_fits_return_wit_9 : fits_return_wit_9
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
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_2 : solver_entail_wit_2
  proof_of_solver_entail_wit_3 : solver_entail_wit_3
  proof_of_solver_entail_wit_4 : solver_entail_wit_4
  proof_of_solver_entail_wit_7 : solver_entail_wit_7
  proof_of_solver_entail_wit_8 : solver_entail_wit_8
  proof_of_solver_entail_wit_9 : solver_entail_wit_9
  proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1
  proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2
  proof_of_solver_entail_wit_10_3 : solver_entail_wit_10_3
  proof_of_solver_entail_wit_10_4 : solver_entail_wit_10_4
  proof_of_solver_entail_wit_10_5 : solver_entail_wit_10_5
  proof_of_solver_entail_wit_10_6 : solver_entail_wit_10_6
  proof_of_solver_entail_wit_10_7 : solver_entail_wit_10_7
  proof_of_solver_entail_wit_10_8 : solver_entail_wit_10_8
  proof_of_solver_entail_wit_10_9 : solver_entail_wit_10_9
  proof_of_solver_entail_wit_10_10 : solver_entail_wit_10_10
  proof_of_solver_entail_wit_10_11 : solver_entail_wit_10_11
  proof_of_solver_entail_wit_10_12 : solver_entail_wit_10_12
  proof_of_solver_return_wit_1 : solver_return_wit_1

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P044_837C_two_seals_goal
