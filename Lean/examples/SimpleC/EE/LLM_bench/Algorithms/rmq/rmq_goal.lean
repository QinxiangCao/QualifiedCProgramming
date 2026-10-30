import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.rmq.rmq_lib
open SimpleC.EE.LLM_bench.Algorithms.rmq.rmq_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.rmq.rmq_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance rmq_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def build_safety_wit_1 : Prop :=
  forall (st0 : (List Int)) (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : (Forall ((LE.le (α := Int)) ((INT_MIN))) l)) (PreH8 : (Forall ((GE.ge (α := Int)) (INT_MAX)) l)) ,
  ((( &( "idx" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st0)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def build_safety_wit_2 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (idx : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : ((0 : Int) <= idx)) (PreH7 : (idx <= (n_pre * K_pre))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((n_pre * K_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre * K_pre)) ”

noncomputable def build_safety_wit_3 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (idx : Int) (PreH1 : (idx < (n_pre * K_pre))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : ((0 : Int) <= idx)) (PreH8 : (idx <= (n_pre * K_pre))) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def build_safety_wit_4 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (idx : Int) (PreH1 : (idx < (n_pre * K_pre))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : ((0 : Int) <= idx)) (PreH8 : (idx <= (n_pre * K_pre))) ,
  (intArray.full st_pre (n_pre * K_pre) (replace_Znth (idx) ((0 : Int)) (st_l)))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "idx" ) )) # Int |-> (idx))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((idx + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (idx + 1)) ”

noncomputable def build_safety_wit_5 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (idx : Int) (PreH1 : (idx >= (n_pre * K_pre))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : ((0 : Int) <= idx)) (PreH8 : (idx <= (n_pre * K_pre))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def build_safety_wit_6 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= (i * K_pre))) (PreH9 : ((i * K_pre) < (n_pre * K_pre))) (PreH10 : (STBasePrefix l st_l K_pre n_pre i)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((i * K_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i * K_pre)) ”

noncomputable def build_safety_wit_7 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= (i * K_pre))) (PreH9 : ((i * K_pre) < (n_pre * K_pre))) (PreH10 : (STBasePrefix l st_l K_pre n_pre i)) ,
  (intArray.full st_pre (n_pre * K_pre) (replace_Znth ((i * K_pre)) ((Znth i l (0 : Int))) (st_l)))
  ** (intArray.full arr_pre n_pre l)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def build_safety_wit_8 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (STBasePrefix l st_l K_pre n_pre i)) ,
  ((( &( "half" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def build_safety_wit_9 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (STBasePrefix l st_l K_pre n_pre i)) ,
  ((( &( "len" ) )) # Int |->_)
  ** ((( &( "half" ) )) # Int |-> (1))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def build_safety_wit_10 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (STBasePrefix l st_l K_pre n_pre i)) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "len" ) )) # Int |-> (2))
  ** ((( &( "half" ) )) # Int |-> (1))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def build_safety_wit_11 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (len : Int) (half : Int) (j : Int) (PreH1 : (j < K_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j <= K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def build_safety_wit_12 : Prop :=
  (
forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (1 <= j)) (PreH7 : (j < K_pre)) (PreH8 : (half = (Power2 ((j - 1))))) (PreH9 : (len = (Power2 (j)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH13 : (STLevelPrefix l st_l K_pre n_pre j i)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((i + len) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + len)) ”
) \/
(
forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (1 <= j)) (PreH7 : (j < K_pre)) (PreH8 : (half = (Power2 ((j - 1))))) (PreH9 : (len = (Power2 (j)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH13 : (STLevelPrefix l st_l K_pre n_pre j i)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((i + len) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + len)) ”
)

noncomputable def build_safety_wit_12_split_goal_1 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (1 <= j)) (PreH7 : (j < K_pre)) (PreH8 : (half = (Power2 ((j - 1))))) (PreH9 : (len = (Power2 (j)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH13 : (STLevelPrefix l st_l K_pre n_pre j i)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((i + len) <= INT_MAX) ”

noncomputable def build_safety_wit_12_split_goal_2 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (1 <= j)) (PreH7 : (j < K_pre)) (PreH8 : (half = (Power2 ((j - 1))))) (PreH9 : (len = (Power2 (j)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH13 : (STLevelPrefix l st_l K_pre n_pre j i)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((INT_MIN) <= (i + len)) ”

noncomputable def build_safety_wit_13 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (1 <= j)) (PreH7 : (j < K_pre)) (PreH8 : (half = (Power2 ((j - 1))))) (PreH9 : (len = (Power2 (j)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : ((i + len) <= n_pre)) (PreH12 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH13 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH15 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH16 : ((0 : Int) <= ((i * K_pre) + j))) (PreH17 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH18 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH19 : (STLevelPrefix l st_l K_pre n_pre j i)) ,
  ((( &( "a" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((((i * K_pre) + j) - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((i * K_pre) + j) - 1)) ”

noncomputable def build_safety_wit_14 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (1 <= j)) (PreH7 : (j < K_pre)) (PreH8 : (half = (Power2 ((j - 1))))) (PreH9 : (len = (Power2 (j)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : ((i + len) <= n_pre)) (PreH12 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH13 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH15 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH16 : ((0 : Int) <= ((i * K_pre) + j))) (PreH17 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH18 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH19 : (STLevelPrefix l st_l K_pre n_pre j i)) ,
  ((( &( "a" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (((i * K_pre) + j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((i * K_pre) + j)) ”

noncomputable def build_safety_wit_15 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (1 <= j)) (PreH7 : (j < K_pre)) (PreH8 : (half = (Power2 ((j - 1))))) (PreH9 : (len = (Power2 (j)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : ((i + len) <= n_pre)) (PreH12 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH13 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH15 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH16 : ((0 : Int) <= ((i * K_pre) + j))) (PreH17 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH18 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH19 : (STLevelPrefix l st_l K_pre n_pre j i)) ,
  ((( &( "a" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((i * K_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i * K_pre)) ”

noncomputable def build_safety_wit_16 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (1 <= j)) (PreH7 : (j < K_pre)) (PreH8 : (half = (Power2 ((j - 1))))) (PreH9 : (len = (Power2 (j)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : ((i + len) <= n_pre)) (PreH12 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH13 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH15 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH16 : ((0 : Int) <= ((i * K_pre) + j))) (PreH17 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH18 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH19 : (STLevelPrefix l st_l K_pre n_pre j i)) ,
  ((( &( "a" ) )) # Int |->_)
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def build_safety_wit_17 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (1 <= j)) (PreH7 : (j < K_pre)) (PreH8 : (half = (Power2 ((j - 1))))) (PreH9 : (len = (Power2 (j)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : ((i + len) <= n_pre)) (PreH12 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH13 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH15 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH16 : ((0 : Int) <= ((i * K_pre) + j))) (PreH17 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH18 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH19 : (STLevelPrefix l st_l K_pre n_pre j i)) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (((((i + half) * K_pre) + j) - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((((i + half) * K_pre) + j) - 1)) ”

noncomputable def build_safety_wit_18 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (1 <= j)) (PreH7 : (j < K_pre)) (PreH8 : (half = (Power2 ((j - 1))))) (PreH9 : (len = (Power2 (j)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : ((i + len) <= n_pre)) (PreH12 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH13 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH15 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH16 : ((0 : Int) <= ((i * K_pre) + j))) (PreH17 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH18 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH19 : (STLevelPrefix l st_l K_pre n_pre j i)) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((((i + half) * K_pre) + j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((i + half) * K_pre) + j)) ”

noncomputable def build_safety_wit_19 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (1 <= j)) (PreH7 : (j < K_pre)) (PreH8 : (half = (Power2 ((j - 1))))) (PreH9 : (len = (Power2 (j)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : ((i + len) <= n_pre)) (PreH12 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH13 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH15 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH16 : ((0 : Int) <= ((i * K_pre) + j))) (PreH17 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH18 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH19 : (STLevelPrefix l st_l K_pre n_pre j i)) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (((i + half) * K_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((i + half) * K_pre)) ”

noncomputable def build_safety_wit_20 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (1 <= j)) (PreH7 : (j < K_pre)) (PreH8 : (half = (Power2 ((j - 1))))) (PreH9 : (len = (Power2 (j)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : ((i + len) <= n_pre)) (PreH12 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH13 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH15 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH16 : ((0 : Int) <= ((i * K_pre) + j))) (PreH17 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH18 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH19 : (STLevelPrefix l st_l K_pre n_pre j i)) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((i + half) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + half)) ”

noncomputable def build_safety_wit_21 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (1 <= j)) (PreH7 : (j < K_pre)) (PreH8 : (half = (Power2 ((j - 1))))) (PreH9 : (len = (Power2 (j)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : ((i + len) <= n_pre)) (PreH12 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH13 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH15 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH16 : ((0 : Int) <= ((i * K_pre) + j))) (PreH17 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH18 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH19 : (STLevelPrefix l st_l K_pre n_pre j i)) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def build_safety_wit_22 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int)) >= (Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j < K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : ((i + len) <= n_pre)) (PreH13 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH14 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH16 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH17 : ((0 : Int) <= ((i * K_pre) + j))) (PreH18 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH19 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH20 : (STLevelPrefix l st_l K_pre n_pre j i)) ,
  (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "b" ) )) # Int |-> ((Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int))))
  ** ((( &( "a" ) )) # Int |-> ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (((i * K_pre) + j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((i * K_pre) + j)) ”

noncomputable def build_safety_wit_23 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int)) >= (Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j < K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : ((i + len) <= n_pre)) (PreH13 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH14 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH16 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH17 : ((0 : Int) <= ((i * K_pre) + j))) (PreH18 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH19 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH20 : (STLevelPrefix l st_l K_pre n_pre j i)) ,
  (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "b" ) )) # Int |-> ((Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int))))
  ** ((( &( "a" ) )) # Int |-> ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((i * K_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i * K_pre)) ”

noncomputable def build_safety_wit_24 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int)) < (Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j < K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : ((i + len) <= n_pre)) (PreH13 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH14 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH16 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH17 : ((0 : Int) <= ((i * K_pre) + j))) (PreH18 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH19 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH20 : (STLevelPrefix l st_l K_pre n_pre j i)) ,
  (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "b" ) )) # Int |-> ((Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int))))
  ** ((( &( "a" ) )) # Int |-> ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
|--
  “ (((i * K_pre) + j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((i * K_pre) + j)) ”

noncomputable def build_safety_wit_25 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int)) < (Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j < K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : ((i + len) <= n_pre)) (PreH13 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH14 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH16 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH17 : ((0 : Int) <= ((i * K_pre) + j))) (PreH18 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH19 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH20 : (STLevelPrefix l st_l K_pre n_pre j i)) ,
  (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "b" ) )) # Int |-> ((Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int))))
  ** ((( &( "a" ) )) # Int |-> ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int))))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((i * K_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i * K_pre)) ”

noncomputable def build_safety_wit_26 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int)) >= (Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j < K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : ((i + len) <= n_pre)) (PreH13 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH14 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH16 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH17 : ((0 : Int) <= ((i * K_pre) + j))) (PreH18 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH19 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH20 : (STLevelPrefix l st_l K_pre n_pre j i)) ,
  (intArray.full st_pre (n_pre * K_pre) (replace_Znth (((i * K_pre) + j)) ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int))) (st_l)))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def build_safety_wit_27 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int)) < (Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j < K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : ((i + len) <= n_pre)) (PreH13 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH14 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH16 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH17 : ((0 : Int) <= ((i * K_pre) + j))) (PreH18 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH19 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH20 : (STLevelPrefix l st_l K_pre n_pre j i)) ,
  (intArray.full st_pre (n_pre * K_pre) (replace_Znth (((i * K_pre) + j)) ((Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int))) (st_l)))
  ** ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (half))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def build_safety_wit_28 : Prop :=
  (
forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (PreH1 : ((i + len) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j < K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH14 : (STLevelPrefix l st_l K_pre n_pre j i)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (len))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((len * 2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (len * 2)) ”
) \/
(
forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (PreH1 : ((i + len) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j < K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH14 : (STLevelPrefix l st_l K_pre n_pre j i)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (len))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((len * 2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (len * 2)) ”
)

noncomputable def build_safety_wit_28_split_goal_1 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (PreH1 : ((i + len) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j < K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH14 : (STLevelPrefix l st_l K_pre n_pre j i)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (len))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((len * 2) <= INT_MAX) ”

noncomputable def build_safety_wit_28_split_goal_2 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (PreH1 : ((i + len) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j < K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH14 : (STLevelPrefix l st_l K_pre n_pre j i)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (len))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((INT_MIN) <= (len * 2)) ”

noncomputable def build_safety_wit_29 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (PreH1 : ((i + len) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j < K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH14 : (STLevelPrefix l st_l K_pre n_pre j i)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (len))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def build_safety_wit_30 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (PreH1 : ((i + len) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j < K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH14 : (STLevelPrefix l st_l K_pre n_pre j i)) ,
  ((( &( "arr" ) )) # Ptr |-> (arr_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "half" ) )) # Int |-> (len))
  ** ((( &( "len" ) )) # Int |-> ((len * 2)))
  ** (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def build_entail_wit_1 : Prop :=
  forall (st0 : (List Int)) (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : (Forall ((LE.le (α := Int)) ((INT_MIN))) l)) (PreH8 : (Forall ((GE.ge (α := Int)) (INT_MAX)) l)) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st0)
|--
  EX st_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= K_pre) ” &&
  “ (K_pre <= 30) ” &&
  “ ((n_pre * K_pre) <= 1000000) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (n_pre * K_pre)) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)

noncomputable def build_entail_wit_2 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l_2 : (List Int)) (idx : Int) (PreH1 : (idx < (n_pre * K_pre))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : ((0 : Int) <= idx)) (PreH8 : (idx <= (n_pre * K_pre))) ,
  (intArray.full st_pre (n_pre * K_pre) (replace_Znth (idx) ((0 : Int)) (st_l_2)))
  ** (intArray.full arr_pre n_pre l)
|--
  EX st_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= K_pre) ” &&
  “ (K_pre <= 30) ” &&
  “ ((n_pre * K_pre) <= 1000000) ” &&
  “ ((0 : Int) <= (idx + 1)) ” &&
  “ ((idx + 1) <= (n_pre * K_pre)) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)

noncomputable def build_entail_wit_3 : Prop :=
  (
forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l_2 : (List Int)) (idx : Int) (PreH1 : (idx >= (n_pre * K_pre))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : ((0 : Int) <= idx)) (PreH8 : (idx <= (n_pre * K_pre))) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l_2)
|--
  EX st_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= K_pre) ” &&
  “ (K_pre <= 30) ” &&
  “ ((n_pre * K_pre) <= 1000000) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (STBasePrefix l st_l K_pre n_pre (0 : Int)) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
) \/
(
forall (l : (List Int)) (n_pre : Int) (K_pre : Int) (st_l_2 : (List Int)) (idx : Int) (PreH1 : (idx >= (n_pre * K_pre))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : ((0 : Int) <= idx)) (PreH8 : (idx <= (n_pre * K_pre))) ,
  TT && emp 
|--
  “ (STBasePrefix l st_l_2 K_pre n_pre (0 : Int)) ”
  &&  emp
)

noncomputable def build_entail_wit_3_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (K_pre : Int) (st_l_2 : (List Int)) (idx : Int) (PreH1 : (idx >= (n_pre * K_pre))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : ((0 : Int) <= idx)) (PreH8 : (idx <= (n_pre * K_pre))) ,
  (STBasePrefix l st_l_2 K_pre n_pre (0 : Int))

noncomputable def build_entail_wit_4 : Prop :=
  (
forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l_2 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (STBasePrefix l st_l_2 K_pre n_pre i)) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l_2)
|--
  EX st_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= K_pre) ” &&
  “ (K_pre <= 30) ” &&
  “ ((n_pre * K_pre) <= 1000000) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= (i * K_pre)) ” &&
  “ ((i * K_pre) < (n_pre * K_pre)) ” &&
  “ (STBasePrefix l st_l K_pre n_pre i) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
) \/
(
forall (l : (List Int)) (n_pre : Int) (K_pre : Int) (st_l_2 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (STBasePrefix l st_l_2 K_pre n_pre i)) ,
  TT && emp 
|--
  “ ((i * K_pre) < (n_pre * K_pre)) ”
  &&  emp
)

noncomputable def build_entail_wit_4_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (K_pre : Int) (st_l_2 : (List Int)) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (STBasePrefix l st_l_2 K_pre n_pre i)) ,
  ((i * K_pre) < (n_pre * K_pre))

noncomputable def build_entail_wit_5 : Prop :=
  (
forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l_2 : (List Int)) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= (i * K_pre))) (PreH9 : ((i * K_pre) < (n_pre * K_pre))) (PreH10 : (STBasePrefix l st_l_2 K_pre n_pre i)) ,
  (intArray.full st_pre (n_pre * K_pre) (replace_Znth ((i * K_pre)) ((Znth i l (0 : Int))) (st_l_2)))
  ** (intArray.full arr_pre n_pre l)
|--
  EX st_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= K_pre) ” &&
  “ (K_pre <= 30) ” &&
  “ ((n_pre * K_pre) <= 1000000) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ (STBasePrefix l st_l K_pre n_pre (i + 1)) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
) \/
(
forall (l : (List Int)) (n_pre : Int) (K_pre : Int) (st_l_2 : (List Int)) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= (i * K_pre))) (PreH9 : ((i * K_pre) < (n_pre * K_pre))) (PreH10 : (STBasePrefix l st_l_2 K_pre n_pre i)) ,
  TT && emp 
|--
  “ (STBasePrefix l (replace_Znth ((i * K_pre)) ((Znth i l (0 : Int))) (st_l_2)) K_pre n_pre (i + 1)) ”
  &&  emp
)

noncomputable def build_entail_wit_5_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (K_pre : Int) (st_l_2 : (List Int)) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= (i * K_pre))) (PreH9 : ((i * K_pre) < (n_pre * K_pre))) (PreH10 : (STBasePrefix l st_l_2 K_pre n_pre i)) ,
  (STBasePrefix l (replace_Znth ((i * K_pre)) ((Znth i l (0 : Int))) (st_l_2)) K_pre n_pre (i + 1))

noncomputable def build_entail_wit_6 : Prop :=
  (
forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l_2 : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (STBasePrefix l st_l_2 K_pre n_pre i)) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l_2)
|--
  EX st_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= K_pre) ” &&
  “ (K_pre <= 30) ” &&
  “ ((n_pre * K_pre) <= 1000000) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= K_pre) ” &&
  “ (1 = (Power2 ((1 - 1)))) ” &&
  “ (2 = (Power2 (1))) ” &&
  “ (STBuiltBeforeLevel l st_l K_pre n_pre 1) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
) \/
(
forall (l : (List Int)) (n_pre : Int) (K_pre : Int) (st_l_2 : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (STBasePrefix l st_l_2 K_pre n_pre i)) ,
  TT && emp 
|--
  “ (STBuiltBeforeLevel l st_l_2 K_pre n_pre 1) ” &&
  “ (2 = (Power2 (1))) ” &&
  “ (1 = (Power2 ((1 - 1)))) ”
  &&  emp
)

noncomputable def build_entail_wit_6_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (K_pre : Int) (st_l_2 : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (STBasePrefix l st_l_2 K_pre n_pre i)) ,
  (STBuiltBeforeLevel l st_l_2 K_pre n_pre 1)

noncomputable def build_entail_wit_6_split_goal_2 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (K_pre : Int) (st_l_2 : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (STBasePrefix l st_l_2 K_pre n_pre i)) ,
  (2 = (Power2 (1)))

noncomputable def build_entail_wit_6_split_goal_3 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (K_pre : Int) (st_l_2 : (List Int)) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (STBasePrefix l st_l_2 K_pre n_pre i)) ,
  (1 = (Power2 ((1 - 1))))

noncomputable def build_entail_wit_7 : Prop :=
  (
forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l_2 : (List Int)) (len : Int) (half : Int) (j : Int) (PreH1 : (j < K_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j <= K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l_2)
|--
  EX st_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= K_pre) ” &&
  “ (K_pre <= 30) ” &&
  “ ((n_pre * K_pre) <= 1000000) ” &&
  “ (1 <= j) ” &&
  “ (j < K_pre) ” &&
  “ (half = (Power2 ((j - 1)))) ” &&
  “ (len = (Power2 (j))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (STBuiltBeforeLevel l st_l K_pre n_pre j) ” &&
  “ (STLevelPrefix l st_l K_pre n_pre j (0 : Int)) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
) \/
(
forall (l : (List Int)) (n_pre : Int) (K_pre : Int) (st_l_2 : (List Int)) (len : Int) (half : Int) (j : Int) (PreH1 : (j < K_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j <= K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) ,
  TT && emp 
|--
  “ (STLevelPrefix l st_l_2 K_pre n_pre j (0 : Int)) ”
  &&  emp
)

noncomputable def build_entail_wit_7_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (K_pre : Int) (st_l_2 : (List Int)) (len : Int) (half : Int) (j : Int) (PreH1 : (j < K_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j <= K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) ,
  (STLevelPrefix l st_l_2 K_pre n_pre j (0 : Int))

noncomputable def build_entail_wit_8 : Prop :=
  (
forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l_2 : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (PreH1 : ((i + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j < K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH14 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l_2)
|--
  EX st_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= K_pre) ” &&
  “ (K_pre <= 30) ” &&
  “ ((n_pre * K_pre) <= 1000000) ” &&
  “ (1 <= j) ” &&
  “ (j < K_pre) ” &&
  “ (half = (Power2 ((j - 1)))) ” &&
  “ (len = (Power2 (j))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ ((i + len) <= n_pre) ” &&
  “ ((0 : Int) <= (((i * K_pre) + j) - 1)) ” &&
  “ ((((i * K_pre) + j) - 1) < (n_pre * K_pre)) ” &&
  “ ((0 : Int) <= ((((i + half) * K_pre) + j) - 1)) ” &&
  “ (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre)) ” &&
  “ ((0 : Int) <= ((i * K_pre) + j)) ” &&
  “ (((i * K_pre) + j) < (n_pre * K_pre)) ” &&
  “ (STBuiltBeforeLevel l st_l K_pre n_pre j) ” &&
  “ (STLevelPrefix l st_l K_pre n_pre j i) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
) \/
(
forall (l : (List Int)) (n_pre : Int) (K_pre : Int) (st_l_2 : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (PreH1 : ((i + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j < K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH14 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  TT && emp 
|--
  “ (((i * K_pre) + j) < (n_pre * K_pre)) ” &&
  “ (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre)) ” &&
  “ ((0 : Int) <= ((((i + half) * K_pre) + j) - 1)) ” &&
  “ ((((i * K_pre) + j) - 1) < (n_pre * K_pre)) ”
  &&  emp
)

noncomputable def build_entail_wit_8_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (K_pre : Int) (st_l_2 : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (PreH1 : ((i + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j < K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH14 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  (((i * K_pre) + j) < (n_pre * K_pre))

noncomputable def build_entail_wit_8_split_goal_2 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (K_pre : Int) (st_l_2 : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (PreH1 : ((i + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j < K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH14 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))

noncomputable def build_entail_wit_8_split_goal_3 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (K_pre : Int) (st_l_2 : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (PreH1 : ((i + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j < K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH14 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))

noncomputable def build_entail_wit_8_split_goal_4 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (K_pre : Int) (st_l_2 : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (PreH1 : ((i + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j < K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH14 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  ((((i * K_pre) + j) - 1) < (n_pre * K_pre))

noncomputable def build_entail_wit_9_1 : Prop :=
  (
forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l_2 : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : ((Znth (((i * K_pre) + j) - 1) st_l_2 (0 : Int)) >= (Znth ((((i + half) * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j < K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : ((i + len) <= n_pre)) (PreH13 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH14 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH16 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH17 : ((0 : Int) <= ((i * K_pre) + j))) (PreH18 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH19 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH20 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  (intArray.full st_pre (n_pre * K_pre) (replace_Znth (((i * K_pre) + j)) ((Znth (((i * K_pre) + j) - 1) st_l_2 (0 : Int))) (st_l_2)))
  ** (intArray.full arr_pre n_pre l)
|--
  EX st_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= K_pre) ” &&
  “ (K_pre <= 30) ” &&
  “ ((n_pre * K_pre) <= 1000000) ” &&
  “ (1 <= j) ” &&
  “ (j < K_pre) ” &&
  “ (half = (Power2 ((j - 1)))) ” &&
  “ (len = (Power2 (j))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ (STBuiltBeforeLevel l st_l K_pre n_pre j) ” &&
  “ (STLevelPrefix l st_l K_pre n_pre j (i + 1)) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
) \/
(
forall (l : (List Int)) (n_pre : Int) (K_pre : Int) (st_l_2 : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : ((Znth (((i * K_pre) + j) - 1) st_l_2 (0 : Int)) >= (Znth ((((i + half) * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j < K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : ((i + len) <= n_pre)) (PreH13 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH14 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH16 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH17 : ((0 : Int) <= ((i * K_pre) + j))) (PreH18 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH19 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH20 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  TT && emp 
|--
  “ (STLevelPrefix l (replace_Znth (((i * K_pre) + j)) ((Znth (((i * K_pre) + j) - 1) st_l_2 (0 : Int))) (st_l_2)) K_pre n_pre j (i + 1)) ” &&
  “ (STBuiltBeforeLevel l (replace_Znth (((i * K_pre) + j)) ((Znth (((i * K_pre) + j) - 1) st_l_2 (0 : Int))) (st_l_2)) K_pre n_pre j) ” &&
  “ ((i + 1) <= n_pre) ”
  &&  emp
)

noncomputable def build_entail_wit_9_1_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (K_pre : Int) (st_l_2 : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : ((Znth (((i * K_pre) + j) - 1) st_l_2 (0 : Int)) >= (Znth ((((i + half) * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j < K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : ((i + len) <= n_pre)) (PreH13 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH14 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH16 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH17 : ((0 : Int) <= ((i * K_pre) + j))) (PreH18 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH19 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH20 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  (STLevelPrefix l (replace_Znth (((i * K_pre) + j)) ((Znth (((i * K_pre) + j) - 1) st_l_2 (0 : Int))) (st_l_2)) K_pre n_pre j (i + 1))

noncomputable def build_entail_wit_9_1_split_goal_2 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (K_pre : Int) (st_l_2 : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : ((Znth (((i * K_pre) + j) - 1) st_l_2 (0 : Int)) >= (Znth ((((i + half) * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j < K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : ((i + len) <= n_pre)) (PreH13 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH14 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH16 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH17 : ((0 : Int) <= ((i * K_pre) + j))) (PreH18 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH19 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH20 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  (STBuiltBeforeLevel l (replace_Znth (((i * K_pre) + j)) ((Znth (((i * K_pre) + j) - 1) st_l_2 (0 : Int))) (st_l_2)) K_pre n_pre j)

noncomputable def build_entail_wit_9_1_split_goal_3 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (K_pre : Int) (st_l_2 : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : ((Znth (((i * K_pre) + j) - 1) st_l_2 (0 : Int)) >= (Znth ((((i + half) * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j < K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : ((i + len) <= n_pre)) (PreH13 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH14 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH16 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH17 : ((0 : Int) <= ((i * K_pre) + j))) (PreH18 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH19 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH20 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  ((i + 1) <= n_pre)

noncomputable def build_entail_wit_9_2 : Prop :=
  (
forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l_2 : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : ((Znth (((i * K_pre) + j) - 1) st_l_2 (0 : Int)) < (Znth ((((i + half) * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j < K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : ((i + len) <= n_pre)) (PreH13 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH14 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH16 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH17 : ((0 : Int) <= ((i * K_pre) + j))) (PreH18 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH19 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH20 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  (intArray.full st_pre (n_pre * K_pre) (replace_Znth (((i * K_pre) + j)) ((Znth ((((i + half) * K_pre) + j) - 1) st_l_2 (0 : Int))) (st_l_2)))
  ** (intArray.full arr_pre n_pre l)
|--
  EX st_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= K_pre) ” &&
  “ (K_pre <= 30) ” &&
  “ ((n_pre * K_pre) <= 1000000) ” &&
  “ (1 <= j) ” &&
  “ (j < K_pre) ” &&
  “ (half = (Power2 ((j - 1)))) ” &&
  “ (len = (Power2 (j))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ (STBuiltBeforeLevel l st_l K_pre n_pre j) ” &&
  “ (STLevelPrefix l st_l K_pre n_pre j (i + 1)) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
) \/
(
forall (l : (List Int)) (n_pre : Int) (K_pre : Int) (st_l_2 : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : ((Znth (((i * K_pre) + j) - 1) st_l_2 (0 : Int)) < (Znth ((((i + half) * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j < K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : ((i + len) <= n_pre)) (PreH13 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH14 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH16 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH17 : ((0 : Int) <= ((i * K_pre) + j))) (PreH18 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH19 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH20 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  TT && emp 
|--
  “ (STLevelPrefix l (replace_Znth (((i * K_pre) + j)) ((Znth ((((i + half) * K_pre) + j) - 1) st_l_2 (0 : Int))) (st_l_2)) K_pre n_pre j (i + 1)) ” &&
  “ (STBuiltBeforeLevel l (replace_Znth (((i * K_pre) + j)) ((Znth ((((i + half) * K_pre) + j) - 1) st_l_2 (0 : Int))) (st_l_2)) K_pre n_pre j) ” &&
  “ ((i + 1) <= n_pre) ”
  &&  emp
)

noncomputable def build_entail_wit_9_2_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (K_pre : Int) (st_l_2 : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : ((Znth (((i * K_pre) + j) - 1) st_l_2 (0 : Int)) < (Znth ((((i + half) * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j < K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : ((i + len) <= n_pre)) (PreH13 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH14 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH16 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH17 : ((0 : Int) <= ((i * K_pre) + j))) (PreH18 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH19 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH20 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  (STLevelPrefix l (replace_Znth (((i * K_pre) + j)) ((Znth ((((i + half) * K_pre) + j) - 1) st_l_2 (0 : Int))) (st_l_2)) K_pre n_pre j (i + 1))

noncomputable def build_entail_wit_9_2_split_goal_2 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (K_pre : Int) (st_l_2 : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : ((Znth (((i * K_pre) + j) - 1) st_l_2 (0 : Int)) < (Znth ((((i + half) * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j < K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : ((i + len) <= n_pre)) (PreH13 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH14 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH16 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH17 : ((0 : Int) <= ((i * K_pre) + j))) (PreH18 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH19 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH20 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  (STBuiltBeforeLevel l (replace_Znth (((i * K_pre) + j)) ((Znth ((((i + half) * K_pre) + j) - 1) st_l_2 (0 : Int))) (st_l_2)) K_pre n_pre j)

noncomputable def build_entail_wit_9_2_split_goal_3 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (K_pre : Int) (st_l_2 : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : ((Znth (((i * K_pre) + j) - 1) st_l_2 (0 : Int)) < (Znth ((((i + half) * K_pre) + j) - 1) st_l_2 (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j < K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : ((i + len) <= n_pre)) (PreH13 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH14 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH16 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH17 : ((0 : Int) <= ((i * K_pre) + j))) (PreH18 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH19 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH20 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  ((i + 1) <= n_pre)

noncomputable def build_entail_wit_10 : Prop :=
  (
forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l_2 : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (PreH1 : ((i + len) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j < K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH14 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l_2)
|--
  EX st_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= K_pre) ” &&
  “ (K_pre <= 30) ” &&
  “ ((n_pre * K_pre) <= 1000000) ” &&
  “ (1 <= (j + 1)) ” &&
  “ ((j + 1) <= K_pre) ” &&
  “ (len = (Power2 (((j + 1) - 1)))) ” &&
  “ ((len * 2) = (Power2 ((j + 1)))) ” &&
  “ (STBuiltBeforeLevel l st_l K_pre n_pre (j + 1)) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
) \/
(
forall (l : (List Int)) (n_pre : Int) (K_pre : Int) (st_l_2 : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (PreH1 : ((i + len) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j < K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH14 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  TT && emp 
|--
  “ (STBuiltBeforeLevel l st_l_2 K_pre n_pre (j + 1)) ” &&
  “ ((len * 2) = (Power2 ((j + 1)))) ” &&
  “ (len = (Power2 (((j + 1) - 1)))) ”
  &&  emp
)

noncomputable def build_entail_wit_10_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (K_pre : Int) (st_l_2 : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (PreH1 : ((i + len) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j < K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH14 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  (STBuiltBeforeLevel l st_l_2 K_pre n_pre (j + 1))

noncomputable def build_entail_wit_10_split_goal_2 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (K_pre : Int) (st_l_2 : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (PreH1 : ((i + len) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j < K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH14 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  ((len * 2) = (Power2 ((j + 1))))

noncomputable def build_entail_wit_10_split_goal_3 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (K_pre : Int) (st_l_2 : (List Int)) (i : Int) (len : Int) (half : Int) (j : Int) (PreH1 : ((i + len) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j < K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) (PreH14 : (STLevelPrefix l st_l_2 K_pre n_pre j i)) ,
  (len = (Power2 (((j + 1) - 1))))

noncomputable def build_return_wit_1 : Prop :=
  (
forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l_2 : (List Int)) (len : Int) (half : Int) (j : Int) (PreH1 : (j >= K_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j <= K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l_2)
|--
  EX st_l : (List Int),
  “ (STBuilt l st_l K_pre n_pre) ”
  &&  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
) \/
(
forall (l : (List Int)) (n_pre : Int) (K_pre : Int) (st_l_2 : (List Int)) (len : Int) (half : Int) (j : Int) (PreH1 : (j >= K_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j <= K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) ,
  TT && emp 
|--
  “ (STBuilt l st_l_2 K_pre n_pre) ”
  &&  emp
)

noncomputable def build_return_wit_1_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (K_pre : Int) (st_l_2 : (List Int)) (len : Int) (half : Int) (j : Int) (PreH1 : (j >= K_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j <= K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j)) ,
  (STBuilt l st_l_2 K_pre n_pre)

noncomputable def build_partial_solve_wit_1 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (idx : Int) (PreH1 : (idx < (n_pre * K_pre))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : ((0 : Int) <= idx)) (PreH8 : (idx <= (n_pre * K_pre))) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (idx < (n_pre * K_pre)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= K_pre) ” &&
  “ (K_pre <= 30) ” &&
  “ ((n_pre * K_pre) <= 1000000) ” &&
  “ ((0 : Int) <= idx) ” &&
  “ (idx <= (n_pre * K_pre)) ”
  &&  (((st_pre + (idx * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i st_pre idx (0 : Int) (n_pre * K_pre) st_l)
  ** (intArray.full arr_pre n_pre l)

noncomputable def build_partial_solve_wit_2 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= (i * K_pre))) (PreH9 : ((i * K_pre) < (n_pre * K_pre))) (PreH10 : (STBasePrefix l st_l K_pre n_pre i)) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= K_pre) ” &&
  “ (K_pre <= 30) ” &&
  “ ((n_pre * K_pre) <= 1000000) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= (i * K_pre)) ” &&
  “ ((i * K_pre) < (n_pre * K_pre)) ” &&
  “ (STBasePrefix l st_l K_pre n_pre i) ”
  &&  (((arr_pre + (i * sizeof(INT)))) # Int |-> ((Znth i l (0 : Int))))
  ** (intArray.missing_i arr_pre i (0 : Int) n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)

noncomputable def build_partial_solve_wit_3 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((0 : Int) <= (i * K_pre))) (PreH9 : ((i * K_pre) < (n_pre * K_pre))) (PreH10 : (STBasePrefix l st_l K_pre n_pre i)) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= K_pre) ” &&
  “ (K_pre <= 30) ” &&
  “ ((n_pre * K_pre) <= 1000000) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= (i * K_pre)) ” &&
  “ ((i * K_pre) < (n_pre * K_pre)) ” &&
  “ (STBasePrefix l st_l K_pre n_pre i) ”
  &&  (((st_pre + ((i * K_pre) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i st_pre (i * K_pre) (0 : Int) (n_pre * K_pre) st_l)
  ** (intArray.full arr_pre n_pre l)

noncomputable def build_partial_solve_wit_4 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (1 <= j)) (PreH7 : (j < K_pre)) (PreH8 : (half = (Power2 ((j - 1))))) (PreH9 : (len = (Power2 (j)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : ((i + len) <= n_pre)) (PreH12 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH13 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH15 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH16 : ((0 : Int) <= ((i * K_pre) + j))) (PreH17 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH18 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH19 : (STLevelPrefix l st_l K_pre n_pre j i)) ,
  (intArray.full arr_pre n_pre l)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= K_pre) ” &&
  “ (K_pre <= 30) ” &&
  “ ((n_pre * K_pre) <= 1000000) ” &&
  “ (1 <= j) ” &&
  “ (j < K_pre) ” &&
  “ (half = (Power2 ((j - 1)))) ” &&
  “ (len = (Power2 (j))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ ((i + len) <= n_pre) ” &&
  “ ((0 : Int) <= (((i * K_pre) + j) - 1)) ” &&
  “ ((((i * K_pre) + j) - 1) < (n_pre * K_pre)) ” &&
  “ ((0 : Int) <= ((((i + half) * K_pre) + j) - 1)) ” &&
  “ (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre)) ” &&
  “ ((0 : Int) <= ((i * K_pre) + j)) ” &&
  “ (((i * K_pre) + j) < (n_pre * K_pre)) ” &&
  “ (STBuiltBeforeLevel l st_l K_pre n_pre j) ” &&
  “ (STLevelPrefix l st_l K_pre n_pre j i) ”
  &&  (((st_pre + ((((i * K_pre) + j) - 1) * sizeof(INT)))) # Int |-> ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int))))
  ** (intArray.missing_i st_pre (((i * K_pre) + j) - 1) (0 : Int) (n_pre * K_pre) st_l)
  ** (intArray.full arr_pre n_pre l)

noncomputable def build_partial_solve_wit_5 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (1 <= j)) (PreH7 : (j < K_pre)) (PreH8 : (half = (Power2 ((j - 1))))) (PreH9 : (len = (Power2 (j)))) (PreH10 : ((0 : Int) <= i)) (PreH11 : ((i + len) <= n_pre)) (PreH12 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH13 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH14 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH15 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH16 : ((0 : Int) <= ((i * K_pre) + j))) (PreH17 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH18 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH19 : (STLevelPrefix l st_l K_pre n_pre j i)) ,
  (intArray.full st_pre (n_pre * K_pre) st_l)
  ** (intArray.full arr_pre n_pre l)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= K_pre) ” &&
  “ (K_pre <= 30) ” &&
  “ ((n_pre * K_pre) <= 1000000) ” &&
  “ (1 <= j) ” &&
  “ (j < K_pre) ” &&
  “ (half = (Power2 ((j - 1)))) ” &&
  “ (len = (Power2 (j))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ ((i + len) <= n_pre) ” &&
  “ ((0 : Int) <= (((i * K_pre) + j) - 1)) ” &&
  “ ((((i * K_pre) + j) - 1) < (n_pre * K_pre)) ” &&
  “ ((0 : Int) <= ((((i + half) * K_pre) + j) - 1)) ” &&
  “ (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre)) ” &&
  “ ((0 : Int) <= ((i * K_pre) + j)) ” &&
  “ (((i * K_pre) + j) < (n_pre * K_pre)) ” &&
  “ (STBuiltBeforeLevel l st_l K_pre n_pre j) ” &&
  “ (STLevelPrefix l st_l K_pre n_pre j i) ”
  &&  (((st_pre + (((((i + half) * K_pre) + j) - 1) * sizeof(INT)))) # Int |-> ((Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int))))
  ** (intArray.missing_i st_pre ((((i + half) * K_pre) + j) - 1) (0 : Int) (n_pre * K_pre) st_l)
  ** (intArray.full arr_pre n_pre l)

noncomputable def build_partial_solve_wit_6 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int)) >= (Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j < K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : ((i + len) <= n_pre)) (PreH13 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH14 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH16 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH17 : ((0 : Int) <= ((i * K_pre) + j))) (PreH18 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH19 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH20 : (STLevelPrefix l st_l K_pre n_pre j i)) ,
  (intArray.full st_pre (n_pre * K_pre) st_l)
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int)) >= (Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= K_pre) ” &&
  “ (K_pre <= 30) ” &&
  “ ((n_pre * K_pre) <= 1000000) ” &&
  “ (1 <= j) ” &&
  “ (j < K_pre) ” &&
  “ (half = (Power2 ((j - 1)))) ” &&
  “ (len = (Power2 (j))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ ((i + len) <= n_pre) ” &&
  “ ((0 : Int) <= (((i * K_pre) + j) - 1)) ” &&
  “ ((((i * K_pre) + j) - 1) < (n_pre * K_pre)) ” &&
  “ ((0 : Int) <= ((((i + half) * K_pre) + j) - 1)) ” &&
  “ (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre)) ” &&
  “ ((0 : Int) <= ((i * K_pre) + j)) ” &&
  “ (((i * K_pre) + j) < (n_pre * K_pre)) ” &&
  “ (STBuiltBeforeLevel l st_l K_pre n_pre j) ” &&
  “ (STLevelPrefix l st_l K_pre n_pre j i) ”
  &&  (((st_pre + (((i * K_pre) + j) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i st_pre ((i * K_pre) + j) (0 : Int) (n_pre * K_pre) st_l)
  ** (intArray.full arr_pre n_pre l)

noncomputable def build_partial_solve_wit_7 : Prop :=
  forall (l : (List Int)) (arr_pre : Int) (n_pre : Int) (K_pre : Int) (st_pre : Int) (st_l : (List Int)) (j : Int) (half : Int) (len : Int) (i : Int) (PreH1 : ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int)) < (Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre) <= 1000000)) (PreH7 : (1 <= j)) (PreH8 : (j < K_pre)) (PreH9 : (half = (Power2 ((j - 1))))) (PreH10 : (len = (Power2 (j)))) (PreH11 : ((0 : Int) <= i)) (PreH12 : ((i + len) <= n_pre)) (PreH13 : ((0 : Int) <= (((i * K_pre) + j) - 1))) (PreH14 : ((((i * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH15 : ((0 : Int) <= ((((i + half) * K_pre) + j) - 1))) (PreH16 : (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre))) (PreH17 : ((0 : Int) <= ((i * K_pre) + j))) (PreH18 : (((i * K_pre) + j) < (n_pre * K_pre))) (PreH19 : (STBuiltBeforeLevel l st_l K_pre n_pre j)) (PreH20 : (STLevelPrefix l st_l K_pre n_pre j i)) ,
  (intArray.full st_pre (n_pre * K_pre) st_l)
  ** (intArray.full arr_pre n_pre l)
|--
  “ ((Znth (((i * K_pre) + j) - 1) st_l (0 : Int)) < (Znth ((((i + half) * K_pre) + j) - 1) st_l (0 : Int))) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ (1 <= K_pre) ” &&
  “ (K_pre <= 30) ” &&
  “ ((n_pre * K_pre) <= 1000000) ” &&
  “ (1 <= j) ” &&
  “ (j < K_pre) ” &&
  “ (half = (Power2 ((j - 1)))) ” &&
  “ (len = (Power2 (j))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ ((i + len) <= n_pre) ” &&
  “ ((0 : Int) <= (((i * K_pre) + j) - 1)) ” &&
  “ ((((i * K_pre) + j) - 1) < (n_pre * K_pre)) ” &&
  “ ((0 : Int) <= ((((i + half) * K_pre) + j) - 1)) ” &&
  “ (((((i + half) * K_pre) + j) - 1) < (n_pre * K_pre)) ” &&
  “ ((0 : Int) <= ((i * K_pre) + j)) ” &&
  “ (((i * K_pre) + j) < (n_pre * K_pre)) ” &&
  “ (STBuiltBeforeLevel l st_l K_pre n_pre j) ” &&
  “ (STLevelPrefix l st_l K_pre n_pre j i) ”
  &&  (((st_pre + (((i * K_pre) + j) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i st_pre ((i * K_pre) + j) (0 : Int) (n_pre * K_pre) st_l)
  ** (intArray.full arr_pre n_pre l)

noncomputable def query_safety_wit_1 : Prop :=
  forall (st_l : (List Int)) (l : (List Int)) (st_pre : Int) (n_pre : Int) (K_pre : Int) (left_pre : Int) (right_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((0 : Int) <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (STBuilt l st_l K_pre n_pre)) ,
  ((( &( "len" ) )) # Int |->_)
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (((right_pre - left_pre) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((right_pre - left_pre) + 1)) ”

noncomputable def query_safety_wit_2 : Prop :=
  forall (st_l : (List Int)) (l : (List Int)) (st_pre : Int) (n_pre : Int) (K_pre : Int) (left_pre : Int) (right_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((0 : Int) <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (STBuilt l st_l K_pre n_pre)) ,
  ((( &( "len" ) )) # Int |->_)
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((right_pre - left_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (right_pre - left_pre)) ”

noncomputable def query_safety_wit_3 : Prop :=
  forall (st_l : (List Int)) (l : (List Int)) (st_pre : Int) (n_pre : Int) (K_pre : Int) (left_pre : Int) (right_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((0 : Int) <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (STBuilt l st_l K_pre n_pre)) ,
  ((( &( "len" ) )) # Int |->_)
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def query_safety_wit_4 : Prop :=
  forall (st_l : (List Int)) (l : (List Int)) (st_pre : Int) (n_pre : Int) (K_pre : Int) (left_pre : Int) (right_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((0 : Int) <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (STBuilt l st_l K_pre n_pre)) ,
  ((( &( "k" ) )) # Int |->_)
  ** ((( &( "len" ) )) # Int |-> (((right_pre - left_pre) + 1)))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def query_safety_wit_5 : Prop :=
  forall (st_l : (List Int)) (l : (List Int)) (st_pre : Int) (n_pre : Int) (K_pre : Int) (left_pre : Int) (right_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((0 : Int) <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (STBuilt l st_l K_pre n_pre)) ,
  ((( &( "pow" ) )) # Int |->_)
  ** ((( &( "k" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "len" ) )) # Int |-> (((right_pre - left_pre) + 1)))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def query_safety_wit_6 : Prop :=
  forall (st_l : (List Int)) (l : (List Int)) (st_pre : Int) (n_pre : Int) (K_pre : Int) (left_pre : Int) (right_pre : Int) (pow : Int) (k : Int) (len : Int) (PreH1 : (n_pre <= 100000)) (PreH2 : (1 <= K_pre)) (PreH3 : (K_pre <= 30)) (PreH4 : ((n_pre * K_pre) <= 1000000)) (PreH5 : (n_pre < (Power2 (K_pre)))) (PreH6 : ((0 : Int) <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre < n_pre)) (PreH9 : (len = ((right_pre - left_pre) + 1))) (PreH10 : ((0 : Int) <= k)) (PreH11 : (k < K_pre)) (PreH12 : (pow = (Power2 (k)))) (PreH13 : (1 <= pow)) (PreH14 : (pow <= len)) (PreH15 : (STBuilt l st_l K_pre n_pre)) ,
  ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((pow * 2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (pow * 2)) ”

noncomputable def query_safety_wit_7 : Prop :=
  forall (st_l : (List Int)) (l : (List Int)) (st_pre : Int) (n_pre : Int) (K_pre : Int) (left_pre : Int) (right_pre : Int) (pow : Int) (k : Int) (len : Int) (PreH1 : (n_pre <= 100000)) (PreH2 : (1 <= K_pre)) (PreH3 : (K_pre <= 30)) (PreH4 : ((n_pre * K_pre) <= 1000000)) (PreH5 : (n_pre < (Power2 (K_pre)))) (PreH6 : ((0 : Int) <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre < n_pre)) (PreH9 : (len = ((right_pre - left_pre) + 1))) (PreH10 : ((0 : Int) <= k)) (PreH11 : (k < K_pre)) (PreH12 : (pow = (Power2 (k)))) (PreH13 : (1 <= pow)) (PreH14 : (pow <= len)) (PreH15 : (STBuilt l st_l K_pre n_pre)) ,
  ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def query_safety_wit_8 : Prop :=
  forall (st_l : (List Int)) (l : (List Int)) (st_pre : Int) (n_pre : Int) (K_pre : Int) (left_pre : Int) (right_pre : Int) (pow : Int) (k : Int) (len : Int) (PreH1 : ((pow * 2) <= len)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((0 : Int) <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : (len = ((right_pre - left_pre) + 1))) (PreH11 : ((0 : Int) <= k)) (PreH12 : (k < K_pre)) (PreH13 : (pow = (Power2 (k)))) (PreH14 : (1 <= pow)) (PreH15 : (pow <= len)) (PreH16 : (STBuilt l st_l K_pre n_pre)) ,
  ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((pow * 2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (pow * 2)) ”

noncomputable def query_safety_wit_9 : Prop :=
  forall (st_l : (List Int)) (l : (List Int)) (st_pre : Int) (n_pre : Int) (K_pre : Int) (left_pre : Int) (right_pre : Int) (pow : Int) (k : Int) (len : Int) (PreH1 : ((pow * 2) <= len)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((0 : Int) <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : (len = ((right_pre - left_pre) + 1))) (PreH11 : ((0 : Int) <= k)) (PreH12 : (k < K_pre)) (PreH13 : (pow = (Power2 (k)))) (PreH14 : (1 <= pow)) (PreH15 : (pow <= len)) (PreH16 : (STBuilt l st_l K_pre n_pre)) ,
  ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def query_safety_wit_10 : Prop :=
  forall (st_l : (List Int)) (l : (List Int)) (st_pre : Int) (n_pre : Int) (K_pre : Int) (left_pre : Int) (right_pre : Int) (pow : Int) (k : Int) (len : Int) (PreH1 : ((pow * 2) <= len)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((0 : Int) <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : (len = ((right_pre - left_pre) + 1))) (PreH11 : ((0 : Int) <= k)) (PreH12 : (k < K_pre)) (PreH13 : (pow = (Power2 (k)))) (PreH14 : (1 <= pow)) (PreH15 : (pow <= len)) (PreH16 : (STBuilt l st_l K_pre n_pre)) ,
  ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "pow" ) )) # Int |-> ((pow * 2)))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def query_safety_wit_11 : Prop :=
  forall (st_l : (List Int)) (l : (List Int)) (st_pre : Int) (n_pre : Int) (K_pre : Int) (left_pre : Int) (right_pre : Int) (len : Int) (k : Int) (pow : Int) (PreH1 : (n_pre <= 100000)) (PreH2 : (1 <= K_pre)) (PreH3 : (K_pre <= 30)) (PreH4 : ((n_pre * K_pre) <= 1000000)) (PreH5 : (n_pre < (Power2 (K_pre)))) (PreH6 : ((0 : Int) <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre < n_pre)) (PreH9 : (len = ((right_pre - left_pre) + 1))) (PreH10 : ((0 : Int) <= k)) (PreH11 : (k < K_pre)) (PreH12 : (pow = (Power2 (k)))) (PreH13 : (1 <= pow)) (PreH14 : (pow <= len)) (PreH15 : (len < (pow * 2))) (PreH16 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH17 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH18 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH19 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH20 : (STBuilt l st_l K_pre n_pre)) ,
  ((( &( "a" ) )) # Int |->_)
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (((left_pre * K_pre) + k) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((left_pre * K_pre) + k)) ”

noncomputable def query_safety_wit_12 : Prop :=
  forall (st_l : (List Int)) (l : (List Int)) (st_pre : Int) (n_pre : Int) (K_pre : Int) (left_pre : Int) (right_pre : Int) (len : Int) (k : Int) (pow : Int) (PreH1 : (n_pre <= 100000)) (PreH2 : (1 <= K_pre)) (PreH3 : (K_pre <= 30)) (PreH4 : ((n_pre * K_pre) <= 1000000)) (PreH5 : (n_pre < (Power2 (K_pre)))) (PreH6 : ((0 : Int) <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre < n_pre)) (PreH9 : (len = ((right_pre - left_pre) + 1))) (PreH10 : ((0 : Int) <= k)) (PreH11 : (k < K_pre)) (PreH12 : (pow = (Power2 (k)))) (PreH13 : (1 <= pow)) (PreH14 : (pow <= len)) (PreH15 : (len < (pow * 2))) (PreH16 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH17 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH18 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH19 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH20 : (STBuilt l st_l K_pre n_pre)) ,
  ((( &( "a" ) )) # Int |->_)
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "pow" ) )) # Int |-> (pow))
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ ((left_pre * K_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left_pre * K_pre)) ”

noncomputable def query_safety_wit_13 : Prop :=
  forall (st_l : (List Int)) (l : (List Int)) (st_pre : Int) (n_pre : Int) (K_pre : Int) (left_pre : Int) (right_pre : Int) (len : Int) (k : Int) (pow : Int) (PreH1 : (n_pre <= 100000)) (PreH2 : (1 <= K_pre)) (PreH3 : (K_pre <= 30)) (PreH4 : ((n_pre * K_pre) <= 1000000)) (PreH5 : (n_pre < (Power2 (K_pre)))) (PreH6 : ((0 : Int) <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre < n_pre)) (PreH9 : (len = ((right_pre - left_pre) + 1))) (PreH10 : ((0 : Int) <= k)) (PreH11 : (k < K_pre)) (PreH12 : (pow = (Power2 (k)))) (PreH13 : (1 <= pow)) (PreH14 : (pow <= len)) (PreH15 : (len < (pow * 2))) (PreH16 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH17 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH18 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH19 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH20 : (STBuilt l st_l K_pre n_pre)) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth ((left_pre * K_pre) + k) st_l (0 : Int))))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "pow" ) )) # Int |-> (pow))
|--
  “ (((((right_pre - pow) + 1) * K_pre) + k) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((((right_pre - pow) + 1) * K_pre) + k)) ”

noncomputable def query_safety_wit_14 : Prop :=
  forall (st_l : (List Int)) (l : (List Int)) (st_pre : Int) (n_pre : Int) (K_pre : Int) (left_pre : Int) (right_pre : Int) (len : Int) (k : Int) (pow : Int) (PreH1 : (n_pre <= 100000)) (PreH2 : (1 <= K_pre)) (PreH3 : (K_pre <= 30)) (PreH4 : ((n_pre * K_pre) <= 1000000)) (PreH5 : (n_pre < (Power2 (K_pre)))) (PreH6 : ((0 : Int) <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre < n_pre)) (PreH9 : (len = ((right_pre - left_pre) + 1))) (PreH10 : ((0 : Int) <= k)) (PreH11 : (k < K_pre)) (PreH12 : (pow = (Power2 (k)))) (PreH13 : (1 <= pow)) (PreH14 : (pow <= len)) (PreH15 : (len < (pow * 2))) (PreH16 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH17 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH18 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH19 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH20 : (STBuilt l st_l K_pre n_pre)) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth ((left_pre * K_pre) + k) st_l (0 : Int))))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "pow" ) )) # Int |-> (pow))
|--
  “ ((((right_pre - pow) + 1) * K_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((right_pre - pow) + 1) * K_pre)) ”

noncomputable def query_safety_wit_15 : Prop :=
  forall (st_l : (List Int)) (l : (List Int)) (st_pre : Int) (n_pre : Int) (K_pre : Int) (left_pre : Int) (right_pre : Int) (len : Int) (k : Int) (pow : Int) (PreH1 : (n_pre <= 100000)) (PreH2 : (1 <= K_pre)) (PreH3 : (K_pre <= 30)) (PreH4 : ((n_pre * K_pre) <= 1000000)) (PreH5 : (n_pre < (Power2 (K_pre)))) (PreH6 : ((0 : Int) <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre < n_pre)) (PreH9 : (len = ((right_pre - left_pre) + 1))) (PreH10 : ((0 : Int) <= k)) (PreH11 : (k < K_pre)) (PreH12 : (pow = (Power2 (k)))) (PreH13 : (1 <= pow)) (PreH14 : (pow <= len)) (PreH15 : (len < (pow * 2))) (PreH16 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH17 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH18 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH19 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH20 : (STBuilt l st_l K_pre n_pre)) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth ((left_pre * K_pre) + k) st_l (0 : Int))))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "pow" ) )) # Int |-> (pow))
|--
  “ (((right_pre - pow) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((right_pre - pow) + 1)) ”

noncomputable def query_safety_wit_16 : Prop :=
  forall (st_l : (List Int)) (l : (List Int)) (st_pre : Int) (n_pre : Int) (K_pre : Int) (left_pre : Int) (right_pre : Int) (len : Int) (k : Int) (pow : Int) (PreH1 : (n_pre <= 100000)) (PreH2 : (1 <= K_pre)) (PreH3 : (K_pre <= 30)) (PreH4 : ((n_pre * K_pre) <= 1000000)) (PreH5 : (n_pre < (Power2 (K_pre)))) (PreH6 : ((0 : Int) <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre < n_pre)) (PreH9 : (len = ((right_pre - left_pre) + 1))) (PreH10 : ((0 : Int) <= k)) (PreH11 : (k < K_pre)) (PreH12 : (pow = (Power2 (k)))) (PreH13 : (1 <= pow)) (PreH14 : (pow <= len)) (PreH15 : (len < (pow * 2))) (PreH16 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH17 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH18 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH19 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH20 : (STBuilt l st_l K_pre n_pre)) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth ((left_pre * K_pre) + k) st_l (0 : Int))))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "pow" ) )) # Int |-> (pow))
|--
  “ ((right_pre - pow) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (right_pre - pow)) ”

noncomputable def query_safety_wit_17 : Prop :=
  forall (st_l : (List Int)) (l : (List Int)) (st_pre : Int) (n_pre : Int) (K_pre : Int) (left_pre : Int) (right_pre : Int) (len : Int) (k : Int) (pow : Int) (PreH1 : (n_pre <= 100000)) (PreH2 : (1 <= K_pre)) (PreH3 : (K_pre <= 30)) (PreH4 : ((n_pre * K_pre) <= 1000000)) (PreH5 : (n_pre < (Power2 (K_pre)))) (PreH6 : ((0 : Int) <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre < n_pre)) (PreH9 : (len = ((right_pre - left_pre) + 1))) (PreH10 : ((0 : Int) <= k)) (PreH11 : (k < K_pre)) (PreH12 : (pow = (Power2 (k)))) (PreH13 : (1 <= pow)) (PreH14 : (pow <= len)) (PreH15 : (len < (pow * 2))) (PreH16 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH17 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH18 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH19 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH20 : (STBuilt l st_l K_pre n_pre)) ,
  ((( &( "b" ) )) # Int |->_)
  ** (intArray.full st_pre (n_pre * K_pre) st_l)
  ** ((( &( "a" ) )) # Int |-> ((Znth ((left_pre * K_pre) + k) st_l (0 : Int))))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "K" ) )) # Int |-> (K_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "pow" ) )) # Int |-> (pow))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def query_entail_wit_1 : Prop :=
  (
forall (st_l : (List Int)) (l : (List Int)) (st_pre : Int) (n_pre : Int) (K_pre : Int) (left_pre : Int) (right_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((0 : Int) <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (STBuilt l st_l K_pre n_pre)) ,
  (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (n_pre <= 100000) ” &&
  “ (1 <= K_pre) ” &&
  “ (K_pre <= 30) ” &&
  “ ((n_pre * K_pre) <= 1000000) ” &&
  “ (n_pre < (Power2 (K_pre))) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= right_pre) ” &&
  “ (right_pre < n_pre) ” &&
  “ (((right_pre - left_pre) + 1) = ((right_pre - left_pre) + 1)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) < K_pre) ” &&
  “ (1 = (Power2 ((0 : Int)))) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= ((right_pre - left_pre) + 1)) ” &&
  “ (STBuilt l st_l K_pre n_pre) ”
  &&  (intArray.full st_pre (n_pre * K_pre) st_l)
) \/
(
forall (st_l : (List Int)) (l : (List Int)) (n_pre : Int) (K_pre : Int) (left_pre : Int) (right_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((0 : Int) <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (STBuilt l st_l K_pre n_pre)) ,
  TT && emp 
|--
  “ (1 = (Power2 ((0 : Int)))) ”
  &&  emp
)

noncomputable def query_entail_wit_1_split_goal_1 : Prop :=
  forall (st_l : (List Int)) (l : (List Int)) (n_pre : Int) (K_pre : Int) (left_pre : Int) (right_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((0 : Int) <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : (STBuilt l st_l K_pre n_pre)) ,
  (1 = (Power2 ((0 : Int))))

noncomputable def query_entail_wit_2 : Prop :=
  (
forall (st_l : (List Int)) (l : (List Int)) (st_pre : Int) (n_pre : Int) (K_pre : Int) (left_pre : Int) (right_pre : Int) (pow : Int) (k : Int) (len : Int) (PreH1 : ((pow * 2) <= len)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((0 : Int) <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : (len = ((right_pre - left_pre) + 1))) (PreH11 : ((0 : Int) <= k)) (PreH12 : (k < K_pre)) (PreH13 : (pow = (Power2 (k)))) (PreH14 : (1 <= pow)) (PreH15 : (pow <= len)) (PreH16 : (STBuilt l st_l K_pre n_pre)) ,
  (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (n_pre <= 100000) ” &&
  “ (1 <= K_pre) ” &&
  “ (K_pre <= 30) ” &&
  “ ((n_pre * K_pre) <= 1000000) ” &&
  “ (n_pre < (Power2 (K_pre))) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= right_pre) ” &&
  “ (right_pre < n_pre) ” &&
  “ (len = ((right_pre - left_pre) + 1)) ” &&
  “ ((0 : Int) <= (k + 1)) ” &&
  “ ((k + 1) < K_pre) ” &&
  “ ((pow * 2) = (Power2 ((k + 1)))) ” &&
  “ (1 <= (pow * 2)) ” &&
  “ ((pow * 2) <= len) ” &&
  “ (STBuilt l st_l K_pre n_pre) ”
  &&  (intArray.full st_pre (n_pre * K_pre) st_l)
) \/
(
forall (st_l : (List Int)) (l : (List Int)) (n_pre : Int) (K_pre : Int) (left_pre : Int) (right_pre : Int) (pow : Int) (k : Int) (len : Int) (PreH1 : ((pow * 2) <= len)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((0 : Int) <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : (len = ((right_pre - left_pre) + 1))) (PreH11 : ((0 : Int) <= k)) (PreH12 : (k < K_pre)) (PreH13 : (pow = (Power2 (k)))) (PreH14 : (1 <= pow)) (PreH15 : (pow <= len)) (PreH16 : (STBuilt l st_l K_pre n_pre)) ,
  TT && emp 
|--
  “ ((pow * 2) = (Power2 ((k + 1)))) ” &&
  “ ((k + 1) < K_pre) ”
  &&  emp
)

noncomputable def query_entail_wit_2_split_goal_1 : Prop :=
  forall (st_l : (List Int)) (l : (List Int)) (n_pre : Int) (K_pre : Int) (left_pre : Int) (right_pre : Int) (pow : Int) (k : Int) (len : Int) (PreH1 : ((pow * 2) <= len)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((0 : Int) <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : (len = ((right_pre - left_pre) + 1))) (PreH11 : ((0 : Int) <= k)) (PreH12 : (k < K_pre)) (PreH13 : (pow = (Power2 (k)))) (PreH14 : (1 <= pow)) (PreH15 : (pow <= len)) (PreH16 : (STBuilt l st_l K_pre n_pre)) ,
  ((pow * 2) = (Power2 ((k + 1))))

noncomputable def query_entail_wit_2_split_goal_2 : Prop :=
  forall (st_l : (List Int)) (l : (List Int)) (n_pre : Int) (K_pre : Int) (left_pre : Int) (right_pre : Int) (pow : Int) (k : Int) (len : Int) (PreH1 : ((pow * 2) <= len)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((0 : Int) <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : (len = ((right_pre - left_pre) + 1))) (PreH11 : ((0 : Int) <= k)) (PreH12 : (k < K_pre)) (PreH13 : (pow = (Power2 (k)))) (PreH14 : (1 <= pow)) (PreH15 : (pow <= len)) (PreH16 : (STBuilt l st_l K_pre n_pre)) ,
  ((k + 1) < K_pre)

noncomputable def query_entail_wit_3 : Prop :=
  (
forall (st_l : (List Int)) (l : (List Int)) (st_pre : Int) (n_pre : Int) (K_pre : Int) (left_pre : Int) (right_pre : Int) (pow : Int) (k : Int) (len : Int) (PreH1 : ((pow * 2) > len)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((0 : Int) <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : (len = ((right_pre - left_pre) + 1))) (PreH11 : ((0 : Int) <= k)) (PreH12 : (k < K_pre)) (PreH13 : (pow = (Power2 (k)))) (PreH14 : (1 <= pow)) (PreH15 : (pow <= len)) (PreH16 : (STBuilt l st_l K_pre n_pre)) ,
  (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (n_pre <= 100000) ” &&
  “ (1 <= K_pre) ” &&
  “ (K_pre <= 30) ” &&
  “ ((n_pre * K_pre) <= 1000000) ” &&
  “ (n_pre < (Power2 (K_pre))) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= right_pre) ” &&
  “ (right_pre < n_pre) ” &&
  “ (len = ((right_pre - left_pre) + 1)) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k < K_pre) ” &&
  “ (pow = (Power2 (k))) ” &&
  “ (1 <= pow) ” &&
  “ (pow <= len) ” &&
  “ (len < (pow * 2)) ” &&
  “ ((0 : Int) <= ((left_pre * K_pre) + k)) ” &&
  “ (((left_pre * K_pre) + k) < (n_pre * K_pre)) ” &&
  “ ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k)) ” &&
  “ (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre)) ” &&
  “ (STBuilt l st_l K_pre n_pre) ”
  &&  (intArray.full st_pre (n_pre * K_pre) st_l)
) \/
(
forall (st_l : (List Int)) (l : (List Int)) (n_pre : Int) (K_pre : Int) (left_pre : Int) (right_pre : Int) (pow : Int) (k : Int) (len : Int) (PreH1 : ((pow * 2) > len)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((0 : Int) <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : (len = ((right_pre - left_pre) + 1))) (PreH11 : ((0 : Int) <= k)) (PreH12 : (k < K_pre)) (PreH13 : (pow = (Power2 (k)))) (PreH14 : (1 <= pow)) (PreH15 : (pow <= len)) (PreH16 : (STBuilt l st_l K_pre n_pre)) ,
  TT && emp 
|--
  “ (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre)) ” &&
  “ ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k)) ” &&
  “ (((left_pre * K_pre) + k) < (n_pre * K_pre)) ”
  &&  emp
)

noncomputable def query_entail_wit_3_split_goal_1 : Prop :=
  forall (st_l : (List Int)) (l : (List Int)) (n_pre : Int) (K_pre : Int) (left_pre : Int) (right_pre : Int) (pow : Int) (k : Int) (len : Int) (PreH1 : ((pow * 2) > len)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((0 : Int) <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : (len = ((right_pre - left_pre) + 1))) (PreH11 : ((0 : Int) <= k)) (PreH12 : (k < K_pre)) (PreH13 : (pow = (Power2 (k)))) (PreH14 : (1 <= pow)) (PreH15 : (pow <= len)) (PreH16 : (STBuilt l st_l K_pre n_pre)) ,
  (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))

noncomputable def query_entail_wit_3_split_goal_2 : Prop :=
  forall (st_l : (List Int)) (l : (List Int)) (n_pre : Int) (K_pre : Int) (left_pre : Int) (right_pre : Int) (pow : Int) (k : Int) (len : Int) (PreH1 : ((pow * 2) > len)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((0 : Int) <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : (len = ((right_pre - left_pre) + 1))) (PreH11 : ((0 : Int) <= k)) (PreH12 : (k < K_pre)) (PreH13 : (pow = (Power2 (k)))) (PreH14 : (1 <= pow)) (PreH15 : (pow <= len)) (PreH16 : (STBuilt l st_l K_pre n_pre)) ,
  ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))

noncomputable def query_entail_wit_3_split_goal_3 : Prop :=
  forall (st_l : (List Int)) (l : (List Int)) (n_pre : Int) (K_pre : Int) (left_pre : Int) (right_pre : Int) (pow : Int) (k : Int) (len : Int) (PreH1 : ((pow * 2) > len)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((0 : Int) <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : (len = ((right_pre - left_pre) + 1))) (PreH11 : ((0 : Int) <= k)) (PreH12 : (k < K_pre)) (PreH13 : (pow = (Power2 (k)))) (PreH14 : (1 <= pow)) (PreH15 : (pow <= len)) (PreH16 : (STBuilt l st_l K_pre n_pre)) ,
  (((left_pre * K_pre) + k) < (n_pre * K_pre))

noncomputable def query_return_wit_1 : Prop :=
  (
forall (st_l : (List Int)) (l : (List Int)) (st_pre : Int) (n_pre : Int) (K_pre : Int) (left_pre : Int) (right_pre : Int) (len : Int) (k : Int) (pow : Int) (PreH1 : ((Znth ((left_pre * K_pre) + k) st_l (0 : Int)) < (Znth ((((right_pre - pow) + 1) * K_pre) + k) st_l (0 : Int)))) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((0 : Int) <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : (len = ((right_pre - left_pre) + 1))) (PreH11 : ((0 : Int) <= k)) (PreH12 : (k < K_pre)) (PreH13 : (pow = (Power2 (k)))) (PreH14 : (1 <= pow)) (PreH15 : (pow <= len)) (PreH16 : (len < (pow * 2))) (PreH17 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH18 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH19 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH20 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH21 : (STBuilt l st_l K_pre n_pre)) ,
  (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (RangeMaxValue l left_pre (right_pre + 1) (Znth ((((right_pre - pow) + 1) * K_pre) + k) st_l (0 : Int))) ”
  &&  (intArray.full st_pre (n_pre * K_pre) st_l)
) \/
(
forall (st_l : (List Int)) (l : (List Int)) (n_pre : Int) (K_pre : Int) (left_pre : Int) (right_pre : Int) (len : Int) (k : Int) (pow : Int) (PreH1 : ((Znth ((left_pre * K_pre) + k) st_l (0 : Int)) < (Znth ((((right_pre - pow) + 1) * K_pre) + k) st_l (0 : Int)))) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((0 : Int) <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : (len = ((right_pre - left_pre) + 1))) (PreH11 : ((0 : Int) <= k)) (PreH12 : (k < K_pre)) (PreH13 : (pow = (Power2 (k)))) (PreH14 : (1 <= pow)) (PreH15 : (pow <= len)) (PreH16 : (len < (pow * 2))) (PreH17 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH18 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH19 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH20 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH21 : (STBuilt l st_l K_pre n_pre)) ,
  TT && emp 
|--
  “ (RangeMaxValue l left_pre (right_pre + 1) (Znth ((((right_pre - pow) + 1) * K_pre) + k) st_l (0 : Int))) ”
  &&  emp
)

noncomputable def query_return_wit_1_split_goal_1 : Prop :=
  forall (st_l : (List Int)) (l : (List Int)) (n_pre : Int) (K_pre : Int) (left_pre : Int) (right_pre : Int) (len : Int) (k : Int) (pow : Int) (PreH1 : ((Znth ((left_pre * K_pre) + k) st_l (0 : Int)) < (Znth ((((right_pre - pow) + 1) * K_pre) + k) st_l (0 : Int)))) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((0 : Int) <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : (len = ((right_pre - left_pre) + 1))) (PreH11 : ((0 : Int) <= k)) (PreH12 : (k < K_pre)) (PreH13 : (pow = (Power2 (k)))) (PreH14 : (1 <= pow)) (PreH15 : (pow <= len)) (PreH16 : (len < (pow * 2))) (PreH17 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH18 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH19 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH20 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH21 : (STBuilt l st_l K_pre n_pre)) ,
  (RangeMaxValue l left_pre (right_pre + 1) (Znth ((((right_pre - pow) + 1) * K_pre) + k) st_l (0 : Int)))

noncomputable def query_return_wit_2 : Prop :=
  (
forall (st_l : (List Int)) (l : (List Int)) (st_pre : Int) (n_pre : Int) (K_pre : Int) (left_pre : Int) (right_pre : Int) (len : Int) (k : Int) (pow : Int) (PreH1 : ((Znth ((left_pre * K_pre) + k) st_l (0 : Int)) >= (Znth ((((right_pre - pow) + 1) * K_pre) + k) st_l (0 : Int)))) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((0 : Int) <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : (len = ((right_pre - left_pre) + 1))) (PreH11 : ((0 : Int) <= k)) (PreH12 : (k < K_pre)) (PreH13 : (pow = (Power2 (k)))) (PreH14 : (1 <= pow)) (PreH15 : (pow <= len)) (PreH16 : (len < (pow * 2))) (PreH17 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH18 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH19 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH20 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH21 : (STBuilt l st_l K_pre n_pre)) ,
  (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (RangeMaxValue l left_pre (right_pre + 1) (Znth ((left_pre * K_pre) + k) st_l (0 : Int))) ”
  &&  (intArray.full st_pre (n_pre * K_pre) st_l)
) \/
(
forall (st_l : (List Int)) (l : (List Int)) (n_pre : Int) (K_pre : Int) (left_pre : Int) (right_pre : Int) (len : Int) (k : Int) (pow : Int) (PreH1 : ((Znth ((left_pre * K_pre) + k) st_l (0 : Int)) >= (Znth ((((right_pre - pow) + 1) * K_pre) + k) st_l (0 : Int)))) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((0 : Int) <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : (len = ((right_pre - left_pre) + 1))) (PreH11 : ((0 : Int) <= k)) (PreH12 : (k < K_pre)) (PreH13 : (pow = (Power2 (k)))) (PreH14 : (1 <= pow)) (PreH15 : (pow <= len)) (PreH16 : (len < (pow * 2))) (PreH17 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH18 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH19 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH20 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH21 : (STBuilt l st_l K_pre n_pre)) ,
  TT && emp 
|--
  “ (RangeMaxValue l left_pre (right_pre + 1) (Znth ((left_pre * K_pre) + k) st_l (0 : Int))) ”
  &&  emp
)

noncomputable def query_return_wit_2_split_goal_1 : Prop :=
  forall (st_l : (List Int)) (l : (List Int)) (n_pre : Int) (K_pre : Int) (left_pre : Int) (right_pre : Int) (len : Int) (k : Int) (pow : Int) (PreH1 : ((Znth ((left_pre * K_pre) + k) st_l (0 : Int)) >= (Znth ((((right_pre - pow) + 1) * K_pre) + k) st_l (0 : Int)))) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((0 : Int) <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : (len = ((right_pre - left_pre) + 1))) (PreH11 : ((0 : Int) <= k)) (PreH12 : (k < K_pre)) (PreH13 : (pow = (Power2 (k)))) (PreH14 : (1 <= pow)) (PreH15 : (pow <= len)) (PreH16 : (len < (pow * 2))) (PreH17 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH18 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH19 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH20 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH21 : (STBuilt l st_l K_pre n_pre)) ,
  (RangeMaxValue l left_pre (right_pre + 1) (Znth ((left_pre * K_pre) + k) st_l (0 : Int)))

noncomputable def query_partial_solve_wit_1 : Prop :=
  forall (st_l : (List Int)) (l : (List Int)) (st_pre : Int) (n_pre : Int) (K_pre : Int) (left_pre : Int) (right_pre : Int) (len : Int) (k : Int) (pow : Int) (PreH1 : (n_pre <= 100000)) (PreH2 : (1 <= K_pre)) (PreH3 : (K_pre <= 30)) (PreH4 : ((n_pre * K_pre) <= 1000000)) (PreH5 : (n_pre < (Power2 (K_pre)))) (PreH6 : ((0 : Int) <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre < n_pre)) (PreH9 : (len = ((right_pre - left_pre) + 1))) (PreH10 : ((0 : Int) <= k)) (PreH11 : (k < K_pre)) (PreH12 : (pow = (Power2 (k)))) (PreH13 : (1 <= pow)) (PreH14 : (pow <= len)) (PreH15 : (len < (pow * 2))) (PreH16 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH17 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH18 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH19 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH20 : (STBuilt l st_l K_pre n_pre)) ,
  (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (n_pre <= 100000) ” &&
  “ (1 <= K_pre) ” &&
  “ (K_pre <= 30) ” &&
  “ ((n_pre * K_pre) <= 1000000) ” &&
  “ (n_pre < (Power2 (K_pre))) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= right_pre) ” &&
  “ (right_pre < n_pre) ” &&
  “ (len = ((right_pre - left_pre) + 1)) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k < K_pre) ” &&
  “ (pow = (Power2 (k))) ” &&
  “ (1 <= pow) ” &&
  “ (pow <= len) ” &&
  “ (len < (pow * 2)) ” &&
  “ ((0 : Int) <= ((left_pre * K_pre) + k)) ” &&
  “ (((left_pre * K_pre) + k) < (n_pre * K_pre)) ” &&
  “ ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k)) ” &&
  “ (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre)) ” &&
  “ (STBuilt l st_l K_pre n_pre) ”
  &&  (((st_pre + (((left_pre * K_pre) + k) * sizeof(INT)))) # Int |-> ((Znth ((left_pre * K_pre) + k) st_l (0 : Int))))
  ** (intArray.missing_i st_pre ((left_pre * K_pre) + k) (0 : Int) (n_pre * K_pre) st_l)

noncomputable def query_partial_solve_wit_2 : Prop :=
  forall (st_l : (List Int)) (l : (List Int)) (st_pre : Int) (n_pre : Int) (K_pre : Int) (left_pre : Int) (right_pre : Int) (len : Int) (k : Int) (pow : Int) (PreH1 : (n_pre <= 100000)) (PreH2 : (1 <= K_pre)) (PreH3 : (K_pre <= 30)) (PreH4 : ((n_pre * K_pre) <= 1000000)) (PreH5 : (n_pre < (Power2 (K_pre)))) (PreH6 : ((0 : Int) <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre < n_pre)) (PreH9 : (len = ((right_pre - left_pre) + 1))) (PreH10 : ((0 : Int) <= k)) (PreH11 : (k < K_pre)) (PreH12 : (pow = (Power2 (k)))) (PreH13 : (1 <= pow)) (PreH14 : (pow <= len)) (PreH15 : (len < (pow * 2))) (PreH16 : ((0 : Int) <= ((left_pre * K_pre) + k))) (PreH17 : (((left_pre * K_pre) + k) < (n_pre * K_pre))) (PreH18 : ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k))) (PreH19 : (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre))) (PreH20 : (STBuilt l st_l K_pre n_pre)) ,
  (intArray.full st_pre (n_pre * K_pre) st_l)
|--
  “ (n_pre <= 100000) ” &&
  “ (1 <= K_pre) ” &&
  “ (K_pre <= 30) ” &&
  “ ((n_pre * K_pre) <= 1000000) ” &&
  “ (n_pre < (Power2 (K_pre))) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= right_pre) ” &&
  “ (right_pre < n_pre) ” &&
  “ (len = ((right_pre - left_pre) + 1)) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k < K_pre) ” &&
  “ (pow = (Power2 (k))) ” &&
  “ (1 <= pow) ” &&
  “ (pow <= len) ” &&
  “ (len < (pow * 2)) ” &&
  “ ((0 : Int) <= ((left_pre * K_pre) + k)) ” &&
  “ (((left_pre * K_pre) + k) < (n_pre * K_pre)) ” &&
  “ ((0 : Int) <= ((((right_pre - pow) + 1) * K_pre) + k)) ” &&
  “ (((((right_pre - pow) + 1) * K_pre) + k) < (n_pre * K_pre)) ” &&
  “ (STBuilt l st_l K_pre n_pre) ”
  &&  (((st_pre + (((((right_pre - pow) + 1) * K_pre) + k) * sizeof(INT)))) # Int |-> ((Znth ((((right_pre - pow) + 1) * K_pre) + k) st_l (0 : Int))))
  ** (intArray.missing_i st_pre ((((right_pre - pow) + 1) * K_pre) + k) (0 : Int) (n_pre * K_pre) st_l)


structure VC_Correct : Type where
  proof_of_build_safety_wit_1 : build_safety_wit_1
  proof_of_build_safety_wit_2 : build_safety_wit_2
  proof_of_build_safety_wit_3 : build_safety_wit_3
  proof_of_build_safety_wit_4 : build_safety_wit_4
  proof_of_build_safety_wit_5 : build_safety_wit_5
  proof_of_build_safety_wit_6 : build_safety_wit_6
  proof_of_build_safety_wit_7 : build_safety_wit_7
  proof_of_build_safety_wit_8 : build_safety_wit_8
  proof_of_build_safety_wit_9 : build_safety_wit_9
  proof_of_build_safety_wit_10 : build_safety_wit_10
  proof_of_build_safety_wit_11 : build_safety_wit_11
  proof_of_build_safety_wit_13 : build_safety_wit_13
  proof_of_build_safety_wit_14 : build_safety_wit_14
  proof_of_build_safety_wit_15 : build_safety_wit_15
  proof_of_build_safety_wit_16 : build_safety_wit_16
  proof_of_build_safety_wit_17 : build_safety_wit_17
  proof_of_build_safety_wit_18 : build_safety_wit_18
  proof_of_build_safety_wit_19 : build_safety_wit_19
  proof_of_build_safety_wit_20 : build_safety_wit_20
  proof_of_build_safety_wit_21 : build_safety_wit_21
  proof_of_build_safety_wit_22 : build_safety_wit_22
  proof_of_build_safety_wit_23 : build_safety_wit_23
  proof_of_build_safety_wit_24 : build_safety_wit_24
  proof_of_build_safety_wit_25 : build_safety_wit_25
  proof_of_build_safety_wit_26 : build_safety_wit_26
  proof_of_build_safety_wit_27 : build_safety_wit_27
  proof_of_build_safety_wit_29 : build_safety_wit_29
  proof_of_build_safety_wit_30 : build_safety_wit_30
  proof_of_build_entail_wit_1 : build_entail_wit_1
  proof_of_build_entail_wit_2 : build_entail_wit_2
  proof_of_build_partial_solve_wit_1 : build_partial_solve_wit_1
  proof_of_build_partial_solve_wit_2 : build_partial_solve_wit_2
  proof_of_build_partial_solve_wit_3 : build_partial_solve_wit_3
  proof_of_build_partial_solve_wit_4 : build_partial_solve_wit_4
  proof_of_build_partial_solve_wit_5 : build_partial_solve_wit_5
  proof_of_build_partial_solve_wit_6 : build_partial_solve_wit_6
  proof_of_build_partial_solve_wit_7 : build_partial_solve_wit_7
  proof_of_query_safety_wit_1 : query_safety_wit_1
  proof_of_query_safety_wit_2 : query_safety_wit_2
  proof_of_query_safety_wit_3 : query_safety_wit_3
  proof_of_query_safety_wit_4 : query_safety_wit_4
  proof_of_query_safety_wit_5 : query_safety_wit_5
  proof_of_query_safety_wit_6 : query_safety_wit_6
  proof_of_query_safety_wit_7 : query_safety_wit_7
  proof_of_query_safety_wit_8 : query_safety_wit_8
  proof_of_query_safety_wit_9 : query_safety_wit_9
  proof_of_query_safety_wit_10 : query_safety_wit_10
  proof_of_query_safety_wit_11 : query_safety_wit_11
  proof_of_query_safety_wit_12 : query_safety_wit_12
  proof_of_query_safety_wit_13 : query_safety_wit_13
  proof_of_query_safety_wit_14 : query_safety_wit_14
  proof_of_query_safety_wit_15 : query_safety_wit_15
  proof_of_query_safety_wit_16 : query_safety_wit_16
  proof_of_query_safety_wit_17 : query_safety_wit_17
  proof_of_query_partial_solve_wit_1 : query_partial_solve_wit_1
  proof_of_query_partial_solve_wit_2 : query_partial_solve_wit_2
  proof_of_build_safety_wit_12 : build_safety_wit_12
  proof_of_build_safety_wit_28 : build_safety_wit_28
  proof_of_build_entail_wit_3 : build_entail_wit_3
  proof_of_build_entail_wit_4 : build_entail_wit_4
  proof_of_build_entail_wit_5 : build_entail_wit_5
  proof_of_build_entail_wit_6 : build_entail_wit_6
  proof_of_build_entail_wit_7 : build_entail_wit_7
  proof_of_build_entail_wit_8 : build_entail_wit_8
  proof_of_build_entail_wit_9_1 : build_entail_wit_9_1
  proof_of_build_entail_wit_9_2 : build_entail_wit_9_2
  proof_of_build_entail_wit_10 : build_entail_wit_10
  proof_of_build_return_wit_1 : build_return_wit_1
  proof_of_query_entail_wit_1 : query_entail_wit_1
  proof_of_query_entail_wit_2 : query_entail_wit_2
  proof_of_query_entail_wit_3 : query_entail_wit_3
  proof_of_query_return_wit_1 : query_return_wit_1
  proof_of_query_return_wit_2 : query_return_wit_2

end SimpleC.EE.LLM_bench.Algorithms.rmq.rmq_goal
