import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P035_807B_t_shirt_hunt_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P035_807B_t_shirt_hunt_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P035_807B_t_shirt_hunt_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P035_807B_t_shirt_hunt_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def wins_safety_wit_1 : Prop :=
  forall (score_pre : Int) (place_pre : Int) (PreH1 : (26 <= place_pre)) (PreH2 : (place_pre <= 500)) (PreH3 : ((0 : Int) <= score_pre)) (PreH4 : (score_pre <= INT_MAX)) ,
  ((( &( "z" ) )) # Int |->_)
  ** ((( &( "place" ) )) # Int |-> (place_pre))
  ** ((( &( "score" ) )) # Int |-> (score_pre))
|--
  “ (((Z.quot score_pre 50) ≠ (INT_MIN)) ∨ (475 ≠ (-1))) ” &&
  “ (475 ≠ (0 : Int)) ”

noncomputable def wins_safety_wit_2 : Prop :=
  forall (score_pre : Int) (place_pre : Int) (PreH1 : (26 <= place_pre)) (PreH2 : (place_pre <= 500)) (PreH3 : ((0 : Int) <= score_pre)) (PreH4 : (score_pre <= INT_MAX)) ,
  ((( &( "z" ) )) # Int |->_)
  ** ((( &( "place" ) )) # Int |-> (place_pre))
  ** ((( &( "score" ) )) # Int |-> (score_pre))
|--
  “ ((score_pre ≠ (INT_MIN)) ∨ (50 ≠ (-1))) ” &&
  “ (50 ≠ (0 : Int)) ”

noncomputable def wins_safety_wit_3 : Prop :=
  forall (score_pre : Int) (place_pre : Int) (PreH1 : (26 <= place_pre)) (PreH2 : (place_pre <= 500)) (PreH3 : ((0 : Int) <= score_pre)) (PreH4 : (score_pre <= INT_MAX)) ,
  ((( &( "z" ) )) # Int |->_)
  ** ((( &( "place" ) )) # Int |-> (place_pre))
  ** ((( &( "score" ) )) # Int |-> (score_pre))
|--
  “ (50 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 50) ”

noncomputable def wins_safety_wit_4 : Prop :=
  forall (score_pre : Int) (place_pre : Int) (PreH1 : (26 <= place_pre)) (PreH2 : (place_pre <= 500)) (PreH3 : ((0 : Int) <= score_pre)) (PreH4 : (score_pre <= INT_MAX)) ,
  ((( &( "z" ) )) # Int |->_)
  ** ((( &( "place" ) )) # Int |-> (place_pre))
  ** ((( &( "score" ) )) # Int |-> (score_pre))
|--
  “ (475 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 475) ”

noncomputable def wins_safety_wit_5 : Prop :=
  forall (score_pre : Int) (place_pre : Int) (PreH1 : (26 <= place_pre)) (PreH2 : (place_pre <= 500)) (PreH3 : ((0 : Int) <= score_pre)) (PreH4 : (score_pre <= INT_MAX)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "z" ) )) # Int |-> ((Z.rem (Z.quot score_pre 50) 475)))
  ** ((( &( "place" ) )) # Int |-> (place_pre))
  ** ((( &( "score" ) )) # Int |-> (score_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def wins_safety_wit_6 : Prop :=
  forall (score_pre : Int) (place_pre : Int) (z : Int) (i : Int) (PreH1 : (26 <= place_pre)) (PreH2 : (place_pre <= 500)) (PreH3 : ((0 : Int) <= score_pre)) (PreH4 : (score_pre <= INT_MAX)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= 25)) (PreH7 : ((0 : Int) <= z)) (PreH8 : (z < 475)) (PreH9 : (ShirtScanState score_pre place_pre i z)) ,
  ((( &( "place" ) )) # Int |-> (place_pre))
  ** ((( &( "score" ) )) # Int |-> (score_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "z" ) )) # Int |-> (z))
|--
  “ (25 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 25) ”

noncomputable def wins_safety_wit_7 : Prop :=
  forall (score_pre : Int) (place_pre : Int) (z : Int) (i : Int) (PreH1 : (i < 25)) (PreH2 : (26 <= place_pre)) (PreH3 : (place_pre <= 500)) (PreH4 : ((0 : Int) <= score_pre)) (PreH5 : (score_pre <= INT_MAX)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= 25)) (PreH8 : ((0 : Int) <= z)) (PreH9 : (z < 475)) (PreH10 : (ShirtScanState score_pre place_pre i z)) ,
  ((( &( "place" ) )) # Int |-> (place_pre))
  ** ((( &( "score" ) )) # Int |-> (score_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "z" ) )) # Int |-> (z))
|--
  “ ((((z * 96) + 42) ≠ (INT_MIN)) ∨ (475 ≠ (-1))) ” &&
  “ (475 ≠ (0 : Int)) ”

noncomputable def wins_safety_wit_8 : Prop :=
  forall (score_pre : Int) (place_pre : Int) (z : Int) (i : Int) (PreH1 : (i < 25)) (PreH2 : (26 <= place_pre)) (PreH3 : (place_pre <= 500)) (PreH4 : ((0 : Int) <= score_pre)) (PreH5 : (score_pre <= INT_MAX)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= 25)) (PreH8 : ((0 : Int) <= z)) (PreH9 : (z < 475)) (PreH10 : (ShirtScanState score_pre place_pre i z)) ,
  ((( &( "place" ) )) # Int |-> (place_pre))
  ** ((( &( "score" ) )) # Int |-> (score_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "z" ) )) # Int |-> (z))
|--
  “ (((z * 96) + 42) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((z * 96) + 42)) ”

noncomputable def wins_safety_wit_9 : Prop :=
  forall (score_pre : Int) (place_pre : Int) (z : Int) (i : Int) (PreH1 : (i < 25)) (PreH2 : (26 <= place_pre)) (PreH3 : (place_pre <= 500)) (PreH4 : ((0 : Int) <= score_pre)) (PreH5 : (score_pre <= INT_MAX)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= 25)) (PreH8 : ((0 : Int) <= z)) (PreH9 : (z < 475)) (PreH10 : (ShirtScanState score_pre place_pre i z)) ,
  ((( &( "place" ) )) # Int |-> (place_pre))
  ** ((( &( "score" ) )) # Int |-> (score_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "z" ) )) # Int |-> (z))
|--
  “ ((z * 96) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (z * 96)) ”

noncomputable def wins_safety_wit_10 : Prop :=
  forall (score_pre : Int) (place_pre : Int) (z : Int) (i : Int) (PreH1 : (i < 25)) (PreH2 : (26 <= place_pre)) (PreH3 : (place_pre <= 500)) (PreH4 : ((0 : Int) <= score_pre)) (PreH5 : (score_pre <= INT_MAX)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= 25)) (PreH8 : ((0 : Int) <= z)) (PreH9 : (z < 475)) (PreH10 : (ShirtScanState score_pre place_pre i z)) ,
  ((( &( "place" ) )) # Int |-> (place_pre))
  ** ((( &( "score" ) )) # Int |-> (score_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "z" ) )) # Int |-> (z))
|--
  “ (96 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 96) ”

noncomputable def wins_safety_wit_11 : Prop :=
  forall (score_pre : Int) (place_pre : Int) (z : Int) (i : Int) (PreH1 : (i < 25)) (PreH2 : (26 <= place_pre)) (PreH3 : (place_pre <= 500)) (PreH4 : ((0 : Int) <= score_pre)) (PreH5 : (score_pre <= INT_MAX)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= 25)) (PreH8 : ((0 : Int) <= z)) (PreH9 : (z < 475)) (PreH10 : (ShirtScanState score_pre place_pre i z)) ,
  ((( &( "place" ) )) # Int |-> (place_pre))
  ** ((( &( "score" ) )) # Int |-> (score_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "z" ) )) # Int |-> (z))
|--
  “ (42 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 42) ”

noncomputable def wins_safety_wit_12 : Prop :=
  forall (score_pre : Int) (place_pre : Int) (z : Int) (i : Int) (PreH1 : (i < 25)) (PreH2 : (26 <= place_pre)) (PreH3 : (place_pre <= 500)) (PreH4 : ((0 : Int) <= score_pre)) (PreH5 : (score_pre <= INT_MAX)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= 25)) (PreH8 : ((0 : Int) <= z)) (PreH9 : (z < 475)) (PreH10 : (ShirtScanState score_pre place_pre i z)) ,
  ((( &( "place" ) )) # Int |-> (place_pre))
  ** ((( &( "score" ) )) # Int |-> (score_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "z" ) )) # Int |-> (z))
|--
  “ (475 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 475) ”

noncomputable def wins_safety_wit_13 : Prop :=
  (
forall (score_pre : Int) (place_pre : Int) (z : Int) (i : Int) (PreH1 : (i < 25)) (PreH2 : (26 <= place_pre)) (PreH3 : (place_pre <= 500)) (PreH4 : ((0 : Int) <= score_pre)) (PreH5 : (score_pre <= INT_MAX)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= 25)) (PreH8 : ((0 : Int) <= z)) (PreH9 : (z < 475)) (PreH10 : (ShirtScanState score_pre place_pre i z)) ,
  ((( &( "place" ) )) # Int |-> (place_pre))
  ** ((( &( "score" ) )) # Int |-> (score_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "z" ) )) # Int |-> ((Z.rem ((z * 96) + 42) 475)))
|--
  “ (((Z.rem ((z * 96) + 42) 475) + 26) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Z.rem ((z * 96) + 42) 475) + 26)) ”
) \/
(
forall (score_pre : Int) (place_pre : Int) (z : Int) (i : Int) (PreH1 : (i < 25)) (PreH2 : (26 <= place_pre)) (PreH3 : (place_pre <= 500)) (PreH4 : ((0 : Int) <= score_pre)) (PreH5 : (score_pre <= INT_MAX)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= 25)) (PreH8 : ((0 : Int) <= z)) (PreH9 : (z < 475)) (PreH10 : (ShirtScanState score_pre place_pre i z)) ,
  ((( &( "place" ) )) # Int |-> (place_pre))
  ** ((( &( "score" ) )) # Int |-> (score_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "z" ) )) # Int |-> ((Z.rem ((z * 96) + 42) 475)))
|--
  “ (((Z.rem ((z * 96) + 42) 475) + 26) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Z.rem ((z * 96) + 42) 475) + 26)) ”
)

noncomputable def wins_safety_wit_13_split_goal_1 : Prop :=
  forall (score_pre : Int) (place_pre : Int) (z : Int) (i : Int) (PreH1 : (i < 25)) (PreH2 : (26 <= place_pre)) (PreH3 : (place_pre <= 500)) (PreH4 : ((0 : Int) <= score_pre)) (PreH5 : (score_pre <= INT_MAX)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= 25)) (PreH8 : ((0 : Int) <= z)) (PreH9 : (z < 475)) (PreH10 : (ShirtScanState score_pre place_pre i z)) ,
  ((( &( "place" ) )) # Int |-> (place_pre))
  ** ((( &( "score" ) )) # Int |-> (score_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "z" ) )) # Int |-> ((Z.rem ((z * 96) + 42) 475)))
|--
  “ (((Z.rem ((z * 96) + 42) 475) + 26) <= INT_MAX) ”

noncomputable def wins_safety_wit_13_split_goal_2 : Prop :=
  forall (score_pre : Int) (place_pre : Int) (z : Int) (i : Int) (PreH1 : (i < 25)) (PreH2 : (26 <= place_pre)) (PreH3 : (place_pre <= 500)) (PreH4 : ((0 : Int) <= score_pre)) (PreH5 : (score_pre <= INT_MAX)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= 25)) (PreH8 : ((0 : Int) <= z)) (PreH9 : (z < 475)) (PreH10 : (ShirtScanState score_pre place_pre i z)) ,
  ((( &( "place" ) )) # Int |-> (place_pre))
  ** ((( &( "score" ) )) # Int |-> (score_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "z" ) )) # Int |-> ((Z.rem ((z * 96) + 42) 475)))
|--
  “ ((INT_MIN) <= ((Z.rem ((z * 96) + 42) 475) + 26)) ”

noncomputable def wins_safety_wit_14 : Prop :=
  forall (score_pre : Int) (place_pre : Int) (z : Int) (i : Int) (PreH1 : (i < 25)) (PreH2 : (26 <= place_pre)) (PreH3 : (place_pre <= 500)) (PreH4 : ((0 : Int) <= score_pre)) (PreH5 : (score_pre <= INT_MAX)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= 25)) (PreH8 : ((0 : Int) <= z)) (PreH9 : (z < 475)) (PreH10 : (ShirtScanState score_pre place_pre i z)) ,
  ((( &( "place" ) )) # Int |-> (place_pre))
  ** ((( &( "score" ) )) # Int |-> (score_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "z" ) )) # Int |-> ((Z.rem ((z * 96) + 42) 475)))
|--
  “ (26 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 26) ”

noncomputable def wins_safety_wit_15 : Prop :=
  forall (score_pre : Int) (place_pre : Int) (z : Int) (i : Int) (PreH1 : (((Z.rem ((z * 96) + 42) 475) + 26) = place_pre)) (PreH2 : (i < 25)) (PreH3 : (26 <= place_pre)) (PreH4 : (place_pre <= 500)) (PreH5 : ((0 : Int) <= score_pre)) (PreH6 : (score_pre <= INT_MAX)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= 25)) (PreH9 : ((0 : Int) <= z)) (PreH10 : (z < 475)) (PreH11 : (ShirtScanState score_pre place_pre i z)) ,
  ((( &( "place" ) )) # Int |-> (place_pre))
  ** ((( &( "score" ) )) # Int |-> (score_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "z" ) )) # Int |-> ((Z.rem ((z * 96) + 42) 475)))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def wins_safety_wit_16 : Prop :=
  forall (score_pre : Int) (place_pre : Int) (z : Int) (i : Int) (PreH1 : (((Z.rem ((z * 96) + 42) 475) + 26) ≠ place_pre)) (PreH2 : (i < 25)) (PreH3 : (26 <= place_pre)) (PreH4 : (place_pre <= 500)) (PreH5 : ((0 : Int) <= score_pre)) (PreH6 : (score_pre <= INT_MAX)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= 25)) (PreH9 : ((0 : Int) <= z)) (PreH10 : (z < 475)) (PreH11 : (ShirtScanState score_pre place_pre i z)) ,
  ((( &( "place" ) )) # Int |-> (place_pre))
  ** ((( &( "score" ) )) # Int |-> (score_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "z" ) )) # Int |-> ((Z.rem ((z * 96) + 42) 475)))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def wins_safety_wit_17 : Prop :=
  forall (score_pre : Int) (place_pre : Int) (z : Int) (i : Int) (PreH1 : (i >= 25)) (PreH2 : (26 <= place_pre)) (PreH3 : (place_pre <= 500)) (PreH4 : ((0 : Int) <= score_pre)) (PreH5 : (score_pre <= INT_MAX)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= 25)) (PreH8 : ((0 : Int) <= z)) (PreH9 : (z < 475)) (PreH10 : (ShirtScanState score_pre place_pre i z)) ,
  ((( &( "place" ) )) # Int |-> (place_pre))
  ** ((( &( "score" ) )) # Int |-> (score_pre))
  ** ((( &( "z" ) )) # Int |-> (z))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def wins_entail_wit_1 : Prop :=
  (
forall (score_pre : Int) (place_pre : Int) (PreH1 : (26 <= place_pre)) (PreH2 : (place_pre <= 500)) (PreH3 : ((0 : Int) <= score_pre)) (PreH4 : (score_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (26 <= place_pre) ” &&
  “ (place_pre <= 500) ” &&
  “ ((0 : Int) <= score_pre) ” &&
  “ (score_pre <= INT_MAX) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 25) ” &&
  “ ((0 : Int) <= (Z.rem (Z.quot score_pre 50) 475)) ” &&
  “ ((Z.rem (Z.quot score_pre 50) 475) < 475) ” &&
  “ (ShirtScanState score_pre place_pre (0 : Int) (Z.rem (Z.quot score_pre 50) 475)) ”
  &&  emp
) \/
(
forall (score_pre : Int) (place_pre : Int) (PreH1 : (26 <= place_pre)) (PreH2 : (place_pre <= 500)) (PreH3 : ((0 : Int) <= score_pre)) (PreH4 : (score_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (ShirtScanState score_pre place_pre (0 : Int) (Z.rem (Z.quot score_pre 50) 475)) ” &&
  “ ((Z.rem (Z.quot score_pre 50) 475) < 475) ” &&
  “ ((0 : Int) <= (Z.rem (Z.quot score_pre 50) 475)) ”
  &&  emp
)

noncomputable def wins_entail_wit_1_split_goal_1 : Prop :=
  forall (score_pre : Int) (place_pre : Int) (PreH1 : (26 <= place_pre)) (PreH2 : (place_pre <= 500)) (PreH3 : ((0 : Int) <= score_pre)) (PreH4 : (score_pre <= INT_MAX)) ,
  (ShirtScanState score_pre place_pre (0 : Int) (Z.rem (Z.quot score_pre 50) 475))

noncomputable def wins_entail_wit_1_split_goal_2 : Prop :=
  forall (score_pre : Int) (place_pre : Int) (PreH1 : (26 <= place_pre)) (PreH2 : (place_pre <= 500)) (PreH3 : ((0 : Int) <= score_pre)) (PreH4 : (score_pre <= INT_MAX)) ,
  ((Z.rem (Z.quot score_pre 50) 475) < 475)

noncomputable def wins_entail_wit_1_split_goal_3 : Prop :=
  forall (score_pre : Int) (place_pre : Int) (PreH1 : (26 <= place_pre)) (PreH2 : (place_pre <= 500)) (PreH3 : ((0 : Int) <= score_pre)) (PreH4 : (score_pre <= INT_MAX)) ,
  ((0 : Int) <= (Z.rem (Z.quot score_pre 50) 475))

noncomputable def wins_entail_wit_2 : Prop :=
  (
forall (score_pre : Int) (place_pre : Int) (z : Int) (i : Int) (PreH1 : (((Z.rem ((z * 96) + 42) 475) + 26) ≠ place_pre)) (PreH2 : (i < 25)) (PreH3 : (26 <= place_pre)) (PreH4 : (place_pre <= 500)) (PreH5 : ((0 : Int) <= score_pre)) (PreH6 : (score_pre <= INT_MAX)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= 25)) (PreH9 : ((0 : Int) <= z)) (PreH10 : (z < 475)) (PreH11 : (ShirtScanState score_pre place_pre i z)) ,
  TT && emp 
|--
  “ (26 <= place_pre) ” &&
  “ (place_pre <= 500) ” &&
  “ ((0 : Int) <= score_pre) ” &&
  “ (score_pre <= INT_MAX) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= 25) ” &&
  “ ((0 : Int) <= (Z.rem ((z * 96) + 42) 475)) ” &&
  “ ((Z.rem ((z * 96) + 42) 475) < 475) ” &&
  “ (ShirtScanState score_pre place_pre (i + 1) (Z.rem ((z * 96) + 42) 475)) ”
  &&  emp
) \/
(
forall (score_pre : Int) (place_pre : Int) (z : Int) (i : Int) (PreH1 : (((Z.rem ((z * 96) + 42) 475) + 26) ≠ place_pre)) (PreH2 : (i < 25)) (PreH3 : (26 <= place_pre)) (PreH4 : (place_pre <= 500)) (PreH5 : ((0 : Int) <= score_pre)) (PreH6 : (score_pre <= INT_MAX)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= 25)) (PreH9 : ((0 : Int) <= z)) (PreH10 : (z < 475)) (PreH11 : (ShirtScanState score_pre place_pre i z)) ,
  TT && emp 
|--
  “ (ShirtScanState score_pre place_pre (i + 1) (Z.rem ((z * 96) + 42) 475)) ” &&
  “ ((Z.rem ((z * 96) + 42) 475) < 475) ” &&
  “ ((0 : Int) <= (Z.rem ((z * 96) + 42) 475)) ”
  &&  emp
)

noncomputable def wins_entail_wit_2_split_goal_1 : Prop :=
  forall (score_pre : Int) (place_pre : Int) (z : Int) (i : Int) (PreH1 : (((Z.rem ((z * 96) + 42) 475) + 26) ≠ place_pre)) (PreH2 : (i < 25)) (PreH3 : (26 <= place_pre)) (PreH4 : (place_pre <= 500)) (PreH5 : ((0 : Int) <= score_pre)) (PreH6 : (score_pre <= INT_MAX)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= 25)) (PreH9 : ((0 : Int) <= z)) (PreH10 : (z < 475)) (PreH11 : (ShirtScanState score_pre place_pre i z)) ,
  (ShirtScanState score_pre place_pre (i + 1) (Z.rem ((z * 96) + 42) 475))

noncomputable def wins_entail_wit_2_split_goal_2 : Prop :=
  forall (score_pre : Int) (place_pre : Int) (z : Int) (i : Int) (PreH1 : (((Z.rem ((z * 96) + 42) 475) + 26) ≠ place_pre)) (PreH2 : (i < 25)) (PreH3 : (26 <= place_pre)) (PreH4 : (place_pre <= 500)) (PreH5 : ((0 : Int) <= score_pre)) (PreH6 : (score_pre <= INT_MAX)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= 25)) (PreH9 : ((0 : Int) <= z)) (PreH10 : (z < 475)) (PreH11 : (ShirtScanState score_pre place_pre i z)) ,
  ((Z.rem ((z * 96) + 42) 475) < 475)

noncomputable def wins_entail_wit_2_split_goal_3 : Prop :=
  forall (score_pre : Int) (place_pre : Int) (z : Int) (i : Int) (PreH1 : (((Z.rem ((z * 96) + 42) 475) + 26) ≠ place_pre)) (PreH2 : (i < 25)) (PreH3 : (26 <= place_pre)) (PreH4 : (place_pre <= 500)) (PreH5 : ((0 : Int) <= score_pre)) (PreH6 : (score_pre <= INT_MAX)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= 25)) (PreH9 : ((0 : Int) <= z)) (PreH10 : (z < 475)) (PreH11 : (ShirtScanState score_pre place_pre i z)) ,
  ((0 : Int) <= (Z.rem ((z * 96) + 42) 475))

noncomputable def wins_return_wit_1 : Prop :=
  (
forall (score_pre : Int) (place_pre : Int) (z : Int) (i : Int) (PreH1 : (i >= 25)) (PreH2 : (26 <= place_pre)) (PreH3 : (place_pre <= 500)) (PreH4 : ((0 : Int) <= score_pre)) (PreH5 : (score_pre <= INT_MAX)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= 25)) (PreH8 : ((0 : Int) <= z)) (PreH9 : (z < 475)) (PreH10 : (ShirtScanState score_pre place_pre i z)) ,
  TT && emp 
|--
  “ ((0 : Int) = (0 : Int)) ” &&
  “ (NoShirtSelection score_pre place_pre) ”
  &&  emp
) \/
(
forall (score_pre : Int) (place_pre : Int) (z : Int) (i : Int) (PreH1 : (i >= 25)) (PreH2 : (26 <= place_pre)) (PreH3 : (place_pre <= 500)) (PreH4 : ((0 : Int) <= score_pre)) (PreH5 : (score_pre <= INT_MAX)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= 25)) (PreH8 : ((0 : Int) <= z)) (PreH9 : (z < 475)) (PreH10 : (ShirtScanState score_pre place_pre i z)) ,
  TT && emp 
|--
  “ (NoShirtSelection score_pre place_pre) ”
  &&  emp
)

noncomputable def wins_return_wit_1_split_goal_1 : Prop :=
  forall (score_pre : Int) (place_pre : Int) (z : Int) (i : Int) (PreH1 : (i >= 25)) (PreH2 : (26 <= place_pre)) (PreH3 : (place_pre <= 500)) (PreH4 : ((0 : Int) <= score_pre)) (PreH5 : (score_pre <= INT_MAX)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= 25)) (PreH8 : ((0 : Int) <= z)) (PreH9 : (z < 475)) (PreH10 : (ShirtScanState score_pre place_pre i z)) ,
  (NoShirtSelection score_pre place_pre)

noncomputable def wins_return_wit_2 : Prop :=
  (
forall (score_pre : Int) (place_pre : Int) (z : Int) (i : Int) (PreH1 : (((Z.rem ((z * 96) + 42) 475) + 26) = place_pre)) (PreH2 : (i < 25)) (PreH3 : (26 <= place_pre)) (PreH4 : (place_pre <= 500)) (PreH5 : ((0 : Int) <= score_pre)) (PreH6 : (score_pre <= INT_MAX)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= 25)) (PreH9 : ((0 : Int) <= z)) (PreH10 : (z < 475)) (PreH11 : (ShirtScanState score_pre place_pre i z)) ,
  TT && emp 
|--
  “ (1 = 1) ” &&
  “ (ShirtSelection score_pre place_pre) ”
  &&  emp
) \/
(
forall (score_pre : Int) (place_pre : Int) (z : Int) (i : Int) (PreH1 : (((Z.rem ((z * 96) + 42) 475) + 26) = place_pre)) (PreH2 : (i < 25)) (PreH3 : (26 <= place_pre)) (PreH4 : (place_pre <= 500)) (PreH5 : ((0 : Int) <= score_pre)) (PreH6 : (score_pre <= INT_MAX)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= 25)) (PreH9 : ((0 : Int) <= z)) (PreH10 : (z < 475)) (PreH11 : (ShirtScanState score_pre place_pre i z)) ,
  TT && emp 
|--
  “ (ShirtSelection score_pre ((Z.rem ((z * 96) + 42) 475) + 26)) ”
  &&  emp
)

noncomputable def wins_return_wit_2_split_goal_1 : Prop :=
  forall (score_pre : Int) (place_pre : Int) (z : Int) (i : Int) (PreH1 : (((Z.rem ((z * 96) + 42) 475) + 26) = place_pre)) (PreH2 : (i < 25)) (PreH3 : (26 <= place_pre)) (PreH4 : (place_pre <= 500)) (PreH5 : ((0 : Int) <= score_pre)) (PreH6 : (score_pre <= INT_MAX)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= 25)) (PreH9 : ((0 : Int) <= z)) (PreH10 : (z < 475)) (PreH11 : (ShirtScanState score_pre place_pre i z)) ,
  (ShirtSelection score_pre ((Z.rem ((z * 96) + 42) 475) + 26))

noncomputable def solver_safety_wit_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (PreH1 : (26 <= p_pre)) (PreH2 : (p_pre <= 500)) (PreH3 : (1 <= y_pre)) (PreH4 : (y_pre <= x_pre)) (PreH5 : (x_pre <= 20000)) (PreH6 : (Pre p_pre x_pre y_pre)) (PreH7 : ((0 : Int) <= (score - y_pre))) (PreH8 : ((score - y_pre) <= 49)) (PreH9 : (AlignmentSearch x_pre y_pre score)) ,
  ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "y" ) )) # Int |-> (y_pre))
  ** ((( &( "score" ) )) # Int |-> (score))
|--
  “ (((score - x_pre) ≠ (INT_MIN)) ∨ (50 ≠ (-1))) ” &&
  “ (50 ≠ (0 : Int)) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (PreH1 : (26 <= p_pre)) (PreH2 : (p_pre <= 500)) (PreH3 : (1 <= y_pre)) (PreH4 : (y_pre <= x_pre)) (PreH5 : (x_pre <= 20000)) (PreH6 : (Pre p_pre x_pre y_pre)) (PreH7 : ((0 : Int) <= (score - y_pre))) (PreH8 : ((score - y_pre) <= 49)) (PreH9 : (AlignmentSearch x_pre y_pre score)) ,
  ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "y" ) )) # Int |-> (y_pre))
  ** ((( &( "score" ) )) # Int |-> (score))
|--
  “ ((score - x_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (score - x_pre)) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (PreH1 : (26 <= p_pre)) (PreH2 : (p_pre <= 500)) (PreH3 : (1 <= y_pre)) (PreH4 : (y_pre <= x_pre)) (PreH5 : (x_pre <= 20000)) (PreH6 : (Pre p_pre x_pre y_pre)) (PreH7 : ((0 : Int) <= (score - y_pre))) (PreH8 : ((score - y_pre) <= 49)) (PreH9 : (AlignmentSearch x_pre y_pre score)) ,
  ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "y" ) )) # Int |-> (y_pre))
  ** ((( &( "score" ) )) # Int |-> (score))
|--
  “ (50 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 50) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (PreH1 : (26 <= p_pre)) (PreH2 : (p_pre <= 500)) (PreH3 : (1 <= y_pre)) (PreH4 : (y_pre <= x_pre)) (PreH5 : (x_pre <= 20000)) (PreH6 : (Pre p_pre x_pre y_pre)) (PreH7 : ((0 : Int) <= (score - y_pre))) (PreH8 : ((score - y_pre) <= 49)) (PreH9 : (AlignmentSearch x_pre y_pre score)) ,
  ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "y" ) )) # Int |-> (y_pre))
  ** ((( &( "score" ) )) # Int |-> (score))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (PreH1 : ((Z.rem (score - x_pre) 50) ≠ (0 : Int))) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (Pre p_pre x_pre y_pre)) (PreH8 : ((0 : Int) <= (score - y_pre))) (PreH9 : ((score - y_pre) <= 49)) (PreH10 : (AlignmentSearch x_pre y_pre score)) ,
  ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "y" ) )) # Int |-> (y_pre))
  ** ((( &( "score" ) )) # Int |-> (score))
|--
  “ ((score + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (score + 1)) ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (retval : Int) (PreH1 : (retval = (0 : Int))) (PreH2 : (retval = 1)) (PreH3 : (ShirtSelection score p_pre)) (PreH4 : (26 <= p_pre)) (PreH5 : (p_pre <= 500)) (PreH6 : (1 <= y_pre)) (PreH7 : (y_pre <= x_pre)) (PreH8 : (x_pre <= 20000)) (PreH9 : (Pre p_pre x_pre y_pre)) (PreH10 : (y_pre <= score)) (PreH11 : (score <= (x_pre + (50 * 475)))) (PreH12 : (CandidateSearch p_pre x_pre y_pre score)) ,
  ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "y" ) )) # Int |-> (y_pre))
  ** ((( &( "score" ) )) # Int |-> (score))
|--
  “ False ”

noncomputable def solver_safety_wit_7 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (retval = (0 : Int))) (PreH3 : (NoShirtSelection score p_pre)) (PreH4 : (26 <= p_pre)) (PreH5 : (p_pre <= 500)) (PreH6 : (1 <= y_pre)) (PreH7 : (y_pre <= x_pre)) (PreH8 : (x_pre <= 20000)) (PreH9 : (Pre p_pre x_pre y_pre)) (PreH10 : (y_pre <= score)) (PreH11 : (score <= (x_pre + (50 * 475)))) (PreH12 : (CandidateSearch p_pre x_pre y_pre score)) ,
  ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "y" ) )) # Int |-> (y_pre))
  ** ((( &( "score" ) )) # Int |-> (score))
|--
  “ False ”

noncomputable def solver_safety_wit_8 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (PreH1 : (26 <= p_pre)) (PreH2 : (p_pre <= 500)) (PreH3 : (1 <= y_pre)) (PreH4 : (y_pre <= x_pre)) (PreH5 : (x_pre <= 20000)) (PreH6 : (Pre p_pre x_pre y_pre)) (PreH7 : (y_pre <= score)) (PreH8 : (score < (x_pre + (50 * 475)))) (PreH9 : (score <= (INT_MAX - 50))) (PreH10 : (CandidateSearch p_pre x_pre y_pre score)) (PreH11 : (NoShirtSelection score p_pre)) ,
  ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "y" ) )) # Int |-> (y_pre))
  ** ((( &( "score" ) )) # Int |-> (score))
|--
  “ ((score + 50) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (score + 50)) ”

noncomputable def solver_safety_wit_9 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (PreH1 : (26 <= p_pre)) (PreH2 : (p_pre <= 500)) (PreH3 : (1 <= y_pre)) (PreH4 : (y_pre <= x_pre)) (PreH5 : (x_pre <= 20000)) (PreH6 : (Pre p_pre x_pre y_pre)) (PreH7 : (y_pre <= score)) (PreH8 : (score < (x_pre + (50 * 475)))) (PreH9 : (score <= (INT_MAX - 50))) (PreH10 : (CandidateSearch p_pre x_pre y_pre score)) (PreH11 : (NoShirtSelection score p_pre)) ,
  ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "y" ) )) # Int |-> (y_pre))
  ** ((( &( "score" ) )) # Int |-> (score))
|--
  “ (50 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 50) ”

noncomputable def solver_safety_wit_10 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (PreH1 : (score <= x_pre)) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (y_pre <= score)) (PreH8 : (score <= (x_pre + (50 * 475)))) (PreH9 : (FirstWinningCandidate p_pre x_pre y_pre score)) ,
  ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "y" ) )) # Int |-> (y_pre))
  ** ((( &( "score" ) )) # Int |-> (score))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_11 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (PreH1 : (score > x_pre)) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (y_pre <= score)) (PreH8 : (score <= (x_pre + (50 * 475)))) (PreH9 : (FirstWinningCandidate p_pre x_pre y_pre score)) ,
  ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "y" ) )) # Int |-> (y_pre))
  ** ((( &( "score" ) )) # Int |-> (score))
|--
  “ ((((score - x_pre) + 99) ≠ (INT_MIN)) ∨ (100 ≠ (-1))) ” &&
  “ (100 ≠ (0 : Int)) ”

noncomputable def solver_safety_wit_12 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (PreH1 : (score > x_pre)) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (y_pre <= score)) (PreH8 : (score <= (x_pre + (50 * 475)))) (PreH9 : (FirstWinningCandidate p_pre x_pre y_pre score)) ,
  ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "y" ) )) # Int |-> (y_pre))
  ** ((( &( "score" ) )) # Int |-> (score))
|--
  “ (((score - x_pre) + 99) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((score - x_pre) + 99)) ”

noncomputable def solver_safety_wit_13 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (PreH1 : (score > x_pre)) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (y_pre <= score)) (PreH8 : (score <= (x_pre + (50 * 475)))) (PreH9 : (FirstWinningCandidate p_pre x_pre y_pre score)) ,
  ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "y" ) )) # Int |-> (y_pre))
  ** ((( &( "score" ) )) # Int |-> (score))
|--
  “ ((score - x_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (score - x_pre)) ”

noncomputable def solver_safety_wit_14 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (PreH1 : (score > x_pre)) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (y_pre <= score)) (PreH8 : (score <= (x_pre + (50 * 475)))) (PreH9 : (FirstWinningCandidate p_pre x_pre y_pre score)) ,
  ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "y" ) )) # Int |-> (y_pre))
  ** ((( &( "score" ) )) # Int |-> (score))
|--
  “ (99 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 99) ”

noncomputable def solver_safety_wit_15 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (PreH1 : (score > x_pre)) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (y_pre <= score)) (PreH8 : (score <= (x_pre + (50 * 475)))) (PreH9 : (FirstWinningCandidate p_pre x_pre y_pre score)) ,
  ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "y" ) )) # Int |-> (y_pre))
  ** ((( &( "score" ) )) # Int |-> (score))
|--
  “ (100 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 100) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (PreH1 : (26 <= p_pre)) (PreH2 : (p_pre <= 500)) (PreH3 : (1 <= y_pre)) (PreH4 : (y_pre <= x_pre)) (PreH5 : (x_pre <= 20000)) (PreH6 : (Pre p_pre x_pre y_pre)) ,
  TT && emp 
|--
  “ (26 <= p_pre) ” &&
  “ (p_pre <= 500) ” &&
  “ (1 <= y_pre) ” &&
  “ (y_pre <= x_pre) ” &&
  “ (x_pre <= 20000) ” &&
  “ (Pre p_pre x_pre y_pre) ” &&
  “ ((0 : Int) <= (y_pre - y_pre)) ” &&
  “ ((y_pre - y_pre) <= 49) ” &&
  “ (AlignmentSearch x_pre y_pre y_pre) ”
  &&  emp
) \/
(
forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (PreH1 : (26 <= p_pre)) (PreH2 : (p_pre <= 500)) (PreH3 : (1 <= y_pre)) (PreH4 : (y_pre <= x_pre)) (PreH5 : (x_pre <= 20000)) (PreH6 : (Pre p_pre x_pre y_pre)) ,
  TT && emp 
|--
  “ (AlignmentSearch x_pre y_pre y_pre) ”
  &&  emp
)

noncomputable def solver_entail_wit_1_split_goal_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (PreH1 : (26 <= p_pre)) (PreH2 : (p_pre <= 500)) (PreH3 : (1 <= y_pre)) (PreH4 : (y_pre <= x_pre)) (PreH5 : (x_pre <= 20000)) (PreH6 : (Pre p_pre x_pre y_pre)) ,
  (AlignmentSearch x_pre y_pre y_pre)

noncomputable def solver_entail_wit_2 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (PreH1 : ((Z.rem (score - x_pre) 50) ≠ (0 : Int))) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (Pre p_pre x_pre y_pre)) (PreH8 : ((0 : Int) <= (score - y_pre))) (PreH9 : ((score - y_pre) <= 49)) (PreH10 : (AlignmentSearch x_pre y_pre score)) ,
  TT && emp 
|--
  “ (26 <= p_pre) ” &&
  “ (p_pre <= 500) ” &&
  “ (1 <= y_pre) ” &&
  “ (y_pre <= x_pre) ” &&
  “ (x_pre <= 20000) ” &&
  “ (Pre p_pre x_pre y_pre) ” &&
  “ ((0 : Int) <= ((score + 1) - y_pre)) ” &&
  “ (((score + 1) - y_pre) <= 49) ” &&
  “ (AlignmentSearch x_pre y_pre (score + 1)) ”
  &&  emp
) \/
(
forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (PreH1 : ((Z.rem (score - x_pre) 50) ≠ (0 : Int))) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (Pre p_pre x_pre y_pre)) (PreH8 : ((0 : Int) <= (score - y_pre))) (PreH9 : ((score - y_pre) <= 49)) (PreH10 : (AlignmentSearch x_pre y_pre score)) ,
  TT && emp 
|--
  “ (AlignmentSearch x_pre y_pre (score + 1)) ” &&
  “ (((score + 1) - y_pre) <= 49) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_split_goal_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (PreH1 : ((Z.rem (score - x_pre) 50) ≠ (0 : Int))) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (Pre p_pre x_pre y_pre)) (PreH8 : ((0 : Int) <= (score - y_pre))) (PreH9 : ((score - y_pre) <= 49)) (PreH10 : (AlignmentSearch x_pre y_pre score)) ,
  (AlignmentSearch x_pre y_pre (score + 1))

noncomputable def solver_entail_wit_2_split_goal_2 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (PreH1 : ((Z.rem (score - x_pre) 50) ≠ (0 : Int))) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (Pre p_pre x_pre y_pre)) (PreH8 : ((0 : Int) <= (score - y_pre))) (PreH9 : ((score - y_pre) <= 49)) (PreH10 : (AlignmentSearch x_pre y_pre score)) ,
  (((score + 1) - y_pre) <= 49)

noncomputable def solver_entail_wit_3 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (PreH1 : ((Z.rem (score - x_pre) 50) = (0 : Int))) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (Pre p_pre x_pre y_pre)) (PreH8 : ((0 : Int) <= (score - y_pre))) (PreH9 : ((score - y_pre) <= 49)) (PreH10 : (AlignmentSearch x_pre y_pre score)) ,
  TT && emp 
|--
  “ (26 <= p_pre) ” &&
  “ (p_pre <= 500) ” &&
  “ (1 <= y_pre) ” &&
  “ (y_pre <= x_pre) ” &&
  “ (x_pre <= 20000) ” &&
  “ (Pre p_pre x_pre y_pre) ” &&
  “ (y_pre <= score) ” &&
  “ (score <= (x_pre + (50 * 475))) ” &&
  “ (CandidateSearch p_pre x_pre y_pre score) ”
  &&  emp
) \/
(
forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (PreH1 : ((Z.rem (score - x_pre) 50) = (0 : Int))) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (Pre p_pre x_pre y_pre)) (PreH8 : ((0 : Int) <= (score - y_pre))) (PreH9 : ((score - y_pre) <= 49)) (PreH10 : (AlignmentSearch x_pre y_pre score)) ,
  TT && emp 
|--
  “ (CandidateSearch p_pre x_pre y_pre score) ”
  &&  emp
)

noncomputable def solver_entail_wit_3_split_goal_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (PreH1 : ((Z.rem (score - x_pre) 50) = (0 : Int))) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (Pre p_pre x_pre y_pre)) (PreH8 : ((0 : Int) <= (score - y_pre))) (PreH9 : ((score - y_pre) <= 49)) (PreH10 : (AlignmentSearch x_pre y_pre score)) ,
  (CandidateSearch p_pre x_pre y_pre score)

noncomputable def solver_entail_wit_4 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (retval : Int) (PreH1 : (retval = (0 : Int))) (PreH2 : (retval = (0 : Int))) (PreH3 : (NoShirtSelection score p_pre)) (PreH4 : (26 <= p_pre)) (PreH5 : (p_pre <= 500)) (PreH6 : (1 <= y_pre)) (PreH7 : (y_pre <= x_pre)) (PreH8 : (x_pre <= 20000)) (PreH9 : (Pre p_pre x_pre y_pre)) (PreH10 : (y_pre <= score)) (PreH11 : (score <= (x_pre + (50 * 475)))) (PreH12 : (CandidateSearch p_pre x_pre y_pre score)) ,
  TT && emp 
|--
  “ (26 <= p_pre) ” &&
  “ (p_pre <= 500) ” &&
  “ (1 <= y_pre) ” &&
  “ (y_pre <= x_pre) ” &&
  “ (x_pre <= 20000) ” &&
  “ (Pre p_pre x_pre y_pre) ” &&
  “ (y_pre <= score) ” &&
  “ (score < (x_pre + (50 * 475))) ” &&
  “ (score <= (INT_MAX - 50)) ” &&
  “ (CandidateSearch p_pre x_pre y_pre score) ” &&
  “ (NoShirtSelection score p_pre) ”
  &&  emp
) \/
(
forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (retval : Int) (PreH1 : (retval = (0 : Int))) (PreH2 : (retval = (0 : Int))) (PreH3 : (NoShirtSelection score p_pre)) (PreH4 : (26 <= p_pre)) (PreH5 : (p_pre <= 500)) (PreH6 : (1 <= y_pre)) (PreH7 : (y_pre <= x_pre)) (PreH8 : (x_pre <= 20000)) (PreH9 : (Pre p_pre x_pre y_pre)) (PreH10 : (y_pre <= score)) (PreH11 : (score <= (x_pre + (50 * 475)))) (PreH12 : (CandidateSearch p_pre x_pre y_pre score)) ,
  TT && emp 
|--
  “ (score < (x_pre + (50 * 475))) ”
  &&  emp
)

noncomputable def solver_entail_wit_4_split_goal_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (retval : Int) (PreH1 : (retval = (0 : Int))) (PreH2 : (retval = (0 : Int))) (PreH3 : (NoShirtSelection score p_pre)) (PreH4 : (26 <= p_pre)) (PreH5 : (p_pre <= 500)) (PreH6 : (1 <= y_pre)) (PreH7 : (y_pre <= x_pre)) (PreH8 : (x_pre <= 20000)) (PreH9 : (Pre p_pre x_pre y_pre)) (PreH10 : (y_pre <= score)) (PreH11 : (score <= (x_pre + (50 * 475)))) (PreH12 : (CandidateSearch p_pre x_pre y_pre score)) ,
  (score < (x_pre + (50 * 475)))

noncomputable def solver_entail_wit_5 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (PreH1 : (26 <= p_pre)) (PreH2 : (p_pre <= 500)) (PreH3 : (1 <= y_pre)) (PreH4 : (y_pre <= x_pre)) (PreH5 : (x_pre <= 20000)) (PreH6 : (Pre p_pre x_pre y_pre)) (PreH7 : (y_pre <= score)) (PreH8 : (score < (x_pre + (50 * 475)))) (PreH9 : (score <= (INT_MAX - 50))) (PreH10 : (CandidateSearch p_pre x_pre y_pre score)) (PreH11 : (NoShirtSelection score p_pre)) ,
  TT && emp 
|--
  “ (26 <= p_pre) ” &&
  “ (p_pre <= 500) ” &&
  “ (1 <= y_pre) ” &&
  “ (y_pre <= x_pre) ” &&
  “ (x_pre <= 20000) ” &&
  “ (Pre p_pre x_pre y_pre) ” &&
  “ (y_pre <= (score + 50)) ” &&
  “ ((score + 50) <= (x_pre + (50 * 475))) ” &&
  “ (CandidateSearch p_pre x_pre y_pre (score + 50)) ”
  &&  emp
) \/
(
forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (PreH1 : (26 <= p_pre)) (PreH2 : (p_pre <= 500)) (PreH3 : (1 <= y_pre)) (PreH4 : (y_pre <= x_pre)) (PreH5 : (x_pre <= 20000)) (PreH6 : (Pre p_pre x_pre y_pre)) (PreH7 : (y_pre <= score)) (PreH8 : (score < (x_pre + (50 * 475)))) (PreH9 : (score <= (INT_MAX - 50))) (PreH10 : (CandidateSearch p_pre x_pre y_pre score)) (PreH11 : (NoShirtSelection score p_pre)) ,
  TT && emp 
|--
  “ (CandidateSearch p_pre x_pre y_pre (score + 50)) ” &&
  “ ((score + 50) <= (x_pre + (50 * 475))) ”
  &&  emp
)

noncomputable def solver_entail_wit_5_split_goal_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (PreH1 : (26 <= p_pre)) (PreH2 : (p_pre <= 500)) (PreH3 : (1 <= y_pre)) (PreH4 : (y_pre <= x_pre)) (PreH5 : (x_pre <= 20000)) (PreH6 : (Pre p_pre x_pre y_pre)) (PreH7 : (y_pre <= score)) (PreH8 : (score < (x_pre + (50 * 475)))) (PreH9 : (score <= (INT_MAX - 50))) (PreH10 : (CandidateSearch p_pre x_pre y_pre score)) (PreH11 : (NoShirtSelection score p_pre)) ,
  (CandidateSearch p_pre x_pre y_pre (score + 50))

noncomputable def solver_entail_wit_5_split_goal_2 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (PreH1 : (26 <= p_pre)) (PreH2 : (p_pre <= 500)) (PreH3 : (1 <= y_pre)) (PreH4 : (y_pre <= x_pre)) (PreH5 : (x_pre <= 20000)) (PreH6 : (Pre p_pre x_pre y_pre)) (PreH7 : (y_pre <= score)) (PreH8 : (score < (x_pre + (50 * 475)))) (PreH9 : (score <= (INT_MAX - 50))) (PreH10 : (CandidateSearch p_pre x_pre y_pre score)) (PreH11 : (NoShirtSelection score p_pre)) ,
  ((score + 50) <= (x_pre + (50 * 475)))

noncomputable def solver_entail_wit_6 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (retval = 1)) (PreH3 : (ShirtSelection score p_pre)) (PreH4 : (26 <= p_pre)) (PreH5 : (p_pre <= 500)) (PreH6 : (1 <= y_pre)) (PreH7 : (y_pre <= x_pre)) (PreH8 : (x_pre <= 20000)) (PreH9 : (Pre p_pre x_pre y_pre)) (PreH10 : (y_pre <= score)) (PreH11 : (score <= (x_pre + (50 * 475)))) (PreH12 : (CandidateSearch p_pre x_pre y_pre score)) ,
  TT && emp 
|--
  “ (26 <= p_pre) ” &&
  “ (p_pre <= 500) ” &&
  “ (1 <= y_pre) ” &&
  “ (y_pre <= x_pre) ” &&
  “ (x_pre <= 20000) ” &&
  “ (y_pre <= score) ” &&
  “ (score <= (x_pre + (50 * 475))) ” &&
  “ (FirstWinningCandidate p_pre x_pre y_pre score) ”
  &&  emp
) \/
(
forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (retval = 1)) (PreH3 : (ShirtSelection score p_pre)) (PreH4 : (26 <= p_pre)) (PreH5 : (p_pre <= 500)) (PreH6 : (1 <= y_pre)) (PreH7 : (y_pre <= x_pre)) (PreH8 : (x_pre <= 20000)) (PreH9 : (Pre p_pre x_pre y_pre)) (PreH10 : (y_pre <= score)) (PreH11 : (score <= (x_pre + (50 * 475)))) (PreH12 : (CandidateSearch p_pre x_pre y_pre score)) ,
  TT && emp 
|--
  “ (FirstWinningCandidate p_pre x_pre y_pre score) ”
  &&  emp
)

noncomputable def solver_entail_wit_6_split_goal_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (retval = 1)) (PreH3 : (ShirtSelection score p_pre)) (PreH4 : (26 <= p_pre)) (PreH5 : (p_pre <= 500)) (PreH6 : (1 <= y_pre)) (PreH7 : (y_pre <= x_pre)) (PreH8 : (x_pre <= 20000)) (PreH9 : (Pre p_pre x_pre y_pre)) (PreH10 : (y_pre <= score)) (PreH11 : (score <= (x_pre + (50 * 475)))) (PreH12 : (CandidateSearch p_pre x_pre y_pre score)) ,
  (FirstWinningCandidate p_pre x_pre y_pre score)

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (PreH1 : (score <= x_pre)) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (y_pre <= score)) (PreH8 : (score <= (x_pre + (50 * 475)))) (PreH9 : (FirstWinningCandidate p_pre x_pre y_pre score)) ,
  TT && emp 
|--
  “ (Spec p_pre x_pre y_pre (0 : Int)) ”
  &&  emp
) \/
(
forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (PreH1 : (score <= x_pre)) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (y_pre <= score)) (PreH8 : (score <= (x_pre + (50 * 475)))) (PreH9 : (FirstWinningCandidate p_pre x_pre y_pre score)) ,
  TT && emp 
|--
  “ (Spec p_pre x_pre y_pre (0 : Int)) ”
  &&  emp
)

noncomputable def solver_return_wit_1_split_goal_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (PreH1 : (score <= x_pre)) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (y_pre <= score)) (PreH8 : (score <= (x_pre + (50 * 475)))) (PreH9 : (FirstWinningCandidate p_pre x_pre y_pre score)) ,
  (Spec p_pre x_pre y_pre (0 : Int))

noncomputable def solver_return_wit_2 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (PreH1 : (score > x_pre)) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (y_pre <= score)) (PreH8 : (score <= (x_pre + (50 * 475)))) (PreH9 : (FirstWinningCandidate p_pre x_pre y_pre score)) ,
  TT && emp 
|--
  “ (Spec p_pre x_pre y_pre (Z.quot ((score - x_pre) + 99) 100)) ”
  &&  emp
) \/
(
forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (PreH1 : (score > x_pre)) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (y_pre <= score)) (PreH8 : (score <= (x_pre + (50 * 475)))) (PreH9 : (FirstWinningCandidate p_pre x_pre y_pre score)) ,
  TT && emp 
|--
  “ (Spec p_pre x_pre y_pre (Z.quot ((score - x_pre) + 99) 100)) ”
  &&  emp
)

noncomputable def solver_return_wit_2_split_goal_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (PreH1 : (score > x_pre)) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (y_pre <= score)) (PreH8 : (score <= (x_pre + (50 * 475)))) (PreH9 : (FirstWinningCandidate p_pre x_pre y_pre score)) ,
  (Spec p_pre x_pre y_pre (Z.quot ((score - x_pre) + 99) 100))

noncomputable def solver_partial_solve_wit_1_pure : Prop :=
  forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (PreH1 : (26 <= p_pre)) (PreH2 : (p_pre <= 500)) (PreH3 : (1 <= y_pre)) (PreH4 : (y_pre <= x_pre)) (PreH5 : (x_pre <= 20000)) (PreH6 : (Pre p_pre x_pre y_pre)) (PreH7 : (y_pre <= score)) (PreH8 : (score <= (x_pre + (50 * 475)))) (PreH9 : (CandidateSearch p_pre x_pre y_pre score)) ,
  ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "y" ) )) # Int |-> (y_pre))
  ** ((( &( "score" ) )) # Int |-> (score))
|--
  “ (26 <= p_pre) ” &&
  “ (p_pre <= 500) ” &&
  “ ((0 : Int) <= score) ” &&
  “ (score <= INT_MAX) ”

noncomputable def solver_partial_solve_wit_1_aux : Prop :=
  forall (y_pre : Int) (x_pre : Int) (p_pre : Int) (score : Int) (PreH1 : (26 <= p_pre)) (PreH2 : (p_pre <= 500)) (PreH3 : (1 <= y_pre)) (PreH4 : (y_pre <= x_pre)) (PreH5 : (x_pre <= 20000)) (PreH6 : (Pre p_pre x_pre y_pre)) (PreH7 : (y_pre <= score)) (PreH8 : (score <= (x_pre + (50 * 475)))) (PreH9 : (CandidateSearch p_pre x_pre y_pre score)) ,
  TT && emp 
|--
  “ (26 <= p_pre) ” &&
  “ (p_pre <= 500) ” &&
  “ ((0 : Int) <= score) ” &&
  “ (score <= INT_MAX) ” &&
  “ (26 <= p_pre) ” &&
  “ (p_pre <= 500) ” &&
  “ (1 <= y_pre) ” &&
  “ (y_pre <= x_pre) ” &&
  “ (x_pre <= 20000) ” &&
  “ (Pre p_pre x_pre y_pre) ” &&
  “ (y_pre <= score) ” &&
  “ (score <= (x_pre + (50 * 475))) ” &&
  “ (CandidateSearch p_pre x_pre y_pre score) ”
  &&  emp

noncomputable def solver_partial_solve_wit_1 : Prop := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux


structure VC_Correct : Type where
  proof_of_wins_safety_wit_1 : wins_safety_wit_1
  proof_of_wins_safety_wit_2 : wins_safety_wit_2
  proof_of_wins_safety_wit_3 : wins_safety_wit_3
  proof_of_wins_safety_wit_4 : wins_safety_wit_4
  proof_of_wins_safety_wit_5 : wins_safety_wit_5
  proof_of_wins_safety_wit_6 : wins_safety_wit_6
  proof_of_wins_safety_wit_7 : wins_safety_wit_7
  proof_of_wins_safety_wit_8 : wins_safety_wit_8
  proof_of_wins_safety_wit_9 : wins_safety_wit_9
  proof_of_wins_safety_wit_10 : wins_safety_wit_10
  proof_of_wins_safety_wit_11 : wins_safety_wit_11
  proof_of_wins_safety_wit_12 : wins_safety_wit_12
  proof_of_wins_safety_wit_14 : wins_safety_wit_14
  proof_of_wins_safety_wit_15 : wins_safety_wit_15
  proof_of_wins_safety_wit_16 : wins_safety_wit_16
  proof_of_wins_safety_wit_17 : wins_safety_wit_17
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
  proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_wins_safety_wit_13 : wins_safety_wit_13
  proof_of_wins_entail_wit_1 : wins_entail_wit_1
  proof_of_wins_entail_wit_2 : wins_entail_wit_2
  proof_of_wins_return_wit_1 : wins_return_wit_1
  proof_of_wins_return_wit_2 : wins_return_wit_2
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_2 : solver_entail_wit_2
  proof_of_solver_entail_wit_3 : solver_entail_wit_3
  proof_of_solver_entail_wit_4 : solver_entail_wit_4
  proof_of_solver_entail_wit_5 : solver_entail_wit_5
  proof_of_solver_entail_wit_6 : solver_entail_wit_6
  proof_of_solver_return_wit_1 : solver_return_wit_1
  proof_of_solver_return_wit_2 : solver_return_wit_2

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P035_807B_t_shirt_hunt_goal
