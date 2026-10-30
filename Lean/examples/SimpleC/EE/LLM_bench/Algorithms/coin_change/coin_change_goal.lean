import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_lib
open SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance coin_change_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def coinChange_safety_wit_1 : Prop :=
  forall (coins_l : (List Int)) (coins_pre : Int) (coinsSize_pre : Int) (amount_pre : Int) (PreH1 : ((0 : Int) <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : ((0 : Int) <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH6 : (Forall ((GE.ge (α := Int)) (INT_MAX)) coins_l)) ,
  (intArray.undef_full ( &( "dp" ) ) 100001)
  ** ((( &( "coins" ) )) # Ptr |-> (coins_pre))
  ** ((( &( "coinsSize" ) )) # Int |-> (coinsSize_pre))
  ** ((( &( "amount" ) )) # Int |-> (amount_pre))
  ** (intArray.full coins_pre coinsSize_pre coins_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def coinChange_safety_wit_2 : Prop :=
  forall (coins_l : (List Int)) (coins_pre : Int) (coinsSize_pre : Int) (amount_pre : Int) (PreH1 : ((0 : Int) <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : ((0 : Int) <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH6 : (Forall ((GE.ge (α := Int)) (INT_MAX)) coins_l)) ,
  (intArray.undef_full ( &( "dp" ) ) 100001)
  ** ((( &( "coins" ) )) # Ptr |-> (coins_pre))
  ** ((( &( "coinsSize" ) )) # Int |-> (coinsSize_pre))
  ** ((( &( "amount" ) )) # Int |-> (amount_pre))
  ** (intArray.full coins_pre coinsSize_pre coins_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def coinChange_safety_wit_3 : Prop :=
  forall (coins_l : (List Int)) (coins_pre : Int) (coinsSize_pre : Int) (amount_pre : Int) (PreH1 : ((0 : Int) <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : ((0 : Int) <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH6 : (Forall ((GE.ge (α := Int)) (INT_MAX)) coins_l)) ,
  ((( &( "j" ) )) # Int |->_)
  ** (((( &( "dp" ) ) + ((0 : Int) * sizeof(INT)))) # Int |-> (1))
  ** (intArray.undef_seg ( &( "dp" ) ) 1 100001)
  ** ((( &( "coins" ) )) # Ptr |-> (coins_pre))
  ** ((( &( "coinsSize" ) )) # Int |-> (coinsSize_pre))
  ** ((( &( "amount" ) )) # Int |-> (amount_pre))
  ** (intArray.full coins_pre coinsSize_pre coins_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def coinChange_safety_wit_4 : Prop :=
  forall (coins_l : (List Int)) (coins_pre : Int) (coinsSize_pre : Int) (amount_pre : Int) (dp_l : (List Int)) (j : Int) (PreH1 : (j <= amount_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (1 <= j)) (PreH6 : (j <= (amount_pre + 1))) (PreH7 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH8 : (DpPrefixZeroed dp_l j)) ,
  ((( &( "coins" ) )) # Ptr |-> (coins_pre))
  ** ((( &( "coinsSize" ) )) # Int |-> (coinsSize_pre))
  ** ((( &( "amount" ) )) # Int |-> (amount_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) j dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) j (amount_pre + 1))
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def coinChange_safety_wit_5 : Prop :=
  forall (coins_l : (List Int)) (coins_pre : Int) (coinsSize_pre : Int) (amount_pre : Int) (dp_l : (List Int)) (j : Int) (PreH1 : (j <= amount_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (1 <= j)) (PreH6 : (j <= (amount_pre + 1))) (PreH7 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH8 : (DpPrefixZeroed dp_l j)) ,
  (intArray.seg ( &( "dp" ) ) (0 : Int) (j + 1) (dp_l ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "dp" ) ) (j + 1) (amount_pre + 1))
  ** ((( &( "coins" ) )) # Ptr |-> (coins_pre))
  ** ((( &( "coinsSize" ) )) # Int |-> (coinsSize_pre))
  ** ((( &( "amount" ) )) # Int |-> (amount_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def coinChange_safety_wit_6 : Prop :=
  forall (coins_l : (List Int)) (coins_pre : Int) (coinsSize_pre : Int) (amount_pre : Int) (dp_l : (List Int)) (j : Int) (PreH1 : (j > amount_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (1 <= j)) (PreH6 : (j <= (amount_pre + 1))) (PreH7 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH8 : (DpPrefixZeroed dp_l j)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "coins" ) )) # Ptr |-> (coins_pre))
  ** ((( &( "coinsSize" ) )) # Int |-> (coinsSize_pre))
  ** ((( &( "amount" ) )) # Int |-> (amount_pre))
  ** (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) j dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) j (amount_pre + 1))
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def coinChange_safety_wit_7 : Prop :=
  forall (coins_l : (List Int)) (coins_pre : Int) (coinsSize_pre : Int) (amount_pre : Int) (dp_l : (List Int)) (j : Int) (coin : Int) (i : Int) (PreH1 : (j <= amount_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (amount_pre <= 100000)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < coinsSize_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH7 : (coin = (Znth i coins_l (0 : Int)))) (PreH8 : (1 <= coin)) (PreH9 : (coin <= amount_pre)) (PreH10 : (coin <= j)) (PreH11 : (j <= (amount_pre + 1))) (PreH12 : (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l j amount_pre)) ,
  ((( &( "coins" ) )) # Ptr |-> (coins_pre))
  ** ((( &( "coinsSize" ) )) # Int |-> (coinsSize_pre))
  ** ((( &( "amount" ) )) # Int |-> (amount_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "coin" ) )) # Int |-> (coin))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full ( &( "dp" ) ) (amount_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
|--
  “ ((j - coin) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j - coin)) ”

noncomputable def coinChange_safety_wit_8 : Prop :=
  forall (coins_l : (List Int)) (coins_pre : Int) (coinsSize_pre : Int) (amount_pre : Int) (dp_l : (List Int)) (j : Int) (coin : Int) (i : Int) (PreH1 : (j <= amount_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (amount_pre <= 100000)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < coinsSize_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH7 : (coin = (Znth i coins_l (0 : Int)))) (PreH8 : (1 <= coin)) (PreH9 : (coin <= amount_pre)) (PreH10 : (coin <= j)) (PreH11 : (j <= (amount_pre + 1))) (PreH12 : (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l j amount_pre)) ,
  (intArray.full ( &( "dp" ) ) (amount_pre + 1) dp_l)
  ** ((( &( "coins" ) )) # Ptr |-> (coins_pre))
  ** ((( &( "coinsSize" ) )) # Int |-> (coinsSize_pre))
  ** ((( &( "amount" ) )) # Int |-> (amount_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "coin" ) )) # Int |-> (coin))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def coinChange_safety_wit_9 : Prop :=
  forall (coins_l : (List Int)) (coins_pre : Int) (coinsSize_pre : Int) (amount_pre : Int) (dp_l : (List Int)) (j : Int) (coin : Int) (i : Int) (PreH1 : ((Znth (j - coin) dp_l (0 : Int)) ≠ (0 : Int))) (PreH2 : (j <= amount_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < coinsSize_pre)) (PreH7 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH8 : (coin = (Znth i coins_l (0 : Int)))) (PreH9 : (1 <= coin)) (PreH10 : (coin <= amount_pre)) (PreH11 : (coin <= j)) (PreH12 : (j <= (amount_pre + 1))) (PreH13 : (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l j amount_pre)) ,
  (intArray.full ( &( "dp" ) ) (amount_pre + 1) dp_l)
  ** ((( &( "coins" ) )) # Ptr |-> (coins_pre))
  ** ((( &( "coinsSize" ) )) # Int |-> (coinsSize_pre))
  ** ((( &( "amount" ) )) # Int |-> (amount_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "coin" ) )) # Int |-> (coin))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def coinChange_safety_wit_10 : Prop :=
  forall (coins_l : (List Int)) (coins_pre : Int) (coinsSize_pre : Int) (amount_pre : Int) (dp_l : (List Int)) (j : Int) (coin : Int) (i : Int) (PreH1 : ((Znth (j - coin) dp_l (0 : Int)) ≠ (0 : Int))) (PreH2 : (j <= amount_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < coinsSize_pre)) (PreH7 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH8 : (coin = (Znth i coins_l (0 : Int)))) (PreH9 : (1 <= coin)) (PreH10 : (coin <= amount_pre)) (PreH11 : (coin <= j)) (PreH12 : (j <= (amount_pre + 1))) (PreH13 : (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l j amount_pre)) ,
  (intArray.full ( &( "dp" ) ) (amount_pre + 1) (replace_Znth (j) (1) (dp_l)))
  ** ((( &( "coins" ) )) # Ptr |-> (coins_pre))
  ** ((( &( "coinsSize" ) )) # Int |-> (coinsSize_pre))
  ** ((( &( "amount" ) )) # Int |-> (amount_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "coin" ) )) # Int |-> (coin))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def coinChange_safety_wit_11 : Prop :=
  forall (coins_l : (List Int)) (coins_pre : Int) (coinsSize_pre : Int) (amount_pre : Int) (dp_l : (List Int)) (j : Int) (coin : Int) (i : Int) (PreH1 : ((Znth (j - coin) dp_l (0 : Int)) = (0 : Int))) (PreH2 : (j <= amount_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < coinsSize_pre)) (PreH7 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH8 : (coin = (Znth i coins_l (0 : Int)))) (PreH9 : (1 <= coin)) (PreH10 : (coin <= amount_pre)) (PreH11 : (coin <= j)) (PreH12 : (j <= (amount_pre + 1))) (PreH13 : (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l j amount_pre)) ,
  (intArray.full ( &( "dp" ) ) (amount_pre + 1) dp_l)
  ** ((( &( "coins" ) )) # Ptr |-> (coins_pre))
  ** ((( &( "coinsSize" ) )) # Int |-> (coinsSize_pre))
  ** ((( &( "amount" ) )) # Int |-> (amount_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "coin" ) )) # Int |-> (coin))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def coinChange_safety_wit_12 : Prop :=
  forall (coins_l : (List Int)) (coins_pre : Int) (coinsSize_pre : Int) (amount_pre : Int) (dp_l : (List Int)) (j : Int) (coin : Int) (i : Int) (PreH1 : (j > amount_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (amount_pre <= 100000)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < coinsSize_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH7 : (coin = (Znth i coins_l (0 : Int)))) (PreH8 : (1 <= coin)) (PreH9 : (coin <= amount_pre)) (PreH10 : (coin <= j)) (PreH11 : (j <= (amount_pre + 1))) (PreH12 : (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l j amount_pre)) ,
  ((( &( "coins" ) )) # Ptr |-> (coins_pre))
  ** ((( &( "coinsSize" ) )) # Int |-> (coinsSize_pre))
  ** ((( &( "amount" ) )) # Int |-> (amount_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full ( &( "dp" ) ) (amount_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def coinChange_safety_wit_13 : Prop :=
  forall (coins_l : (List Int)) (coins_pre : Int) (coinsSize_pre : Int) (amount_pre : Int) (dp_l : (List Int)) (i : Int) (PreH1 : ((Znth i coins_l (0 : Int)) > amount_pre)) (PreH2 : (i < coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= coinsSize_pre)) (PreH8 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH9 : (DpReachableTable (sublist ((0 : Int)) (i) (coins_l)) dp_l (amount_pre + 1))) ,
  (intArray.full coins_pre coinsSize_pre coins_l)
  ** ((( &( "coins" ) )) # Ptr |-> (coins_pre))
  ** ((( &( "coinsSize" ) )) # Int |-> (coinsSize_pre))
  ** ((( &( "amount" ) )) # Int |-> (amount_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full ( &( "dp" ) ) (amount_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def coinChange_safety_wit_14 : Prop :=
  forall (coins_l : (List Int)) (coins_pre : Int) (coinsSize_pre : Int) (amount_pre : Int) (dp_l : (List Int)) (res : Int) (PreH1 : ((0 : Int) <= res)) (PreH2 : (res <= amount_pre)) (PreH3 : (DpReachableTable coins_l dp_l (amount_pre + 1))) (PreH4 : (NoReachableAbove coins_l amount_pre res)) ,
  ((( &( "coins" ) )) # Ptr |-> (coins_pre))
  ** ((( &( "coinsSize" ) )) # Int |-> (coinsSize_pre))
  ** ((( &( "amount" ) )) # Int |-> (amount_pre))
  ** ((( &( "res" ) )) # Int |-> (res))
  ** (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full ( &( "dp" ) ) (amount_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def coinChange_safety_wit_15 : Prop :=
  forall (coins_l : (List Int)) (coins_pre : Int) (coinsSize_pre : Int) (amount_pre : Int) (dp_l : (List Int)) (res : Int) (PreH1 : (res > (0 : Int))) (PreH2 : ((0 : Int) <= res)) (PreH3 : (res <= amount_pre)) (PreH4 : (DpReachableTable coins_l dp_l (amount_pre + 1))) (PreH5 : (NoReachableAbove coins_l amount_pre res)) ,
  (intArray.full ( &( "dp" ) ) (amount_pre + 1) dp_l)
  ** ((( &( "coins" ) )) # Ptr |-> (coins_pre))
  ** ((( &( "coinsSize" ) )) # Int |-> (coinsSize_pre))
  ** ((( &( "amount" ) )) # Int |-> (amount_pre))
  ** ((( &( "res" ) )) # Int |-> (res))
  ** (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def coinChange_safety_wit_16 : Prop :=
  forall (coins_l : (List Int)) (coins_pre : Int) (coinsSize_pre : Int) (amount_pre : Int) (dp_l : (List Int)) (res : Int) (PreH1 : ((Znth res dp_l (0 : Int)) = (0 : Int))) (PreH2 : (res > (0 : Int))) (PreH3 : ((0 : Int) <= res)) (PreH4 : (res <= amount_pre)) (PreH5 : (DpReachableTable coins_l dp_l (amount_pre + 1))) (PreH6 : (NoReachableAbove coins_l amount_pre res)) ,
  (intArray.full ( &( "dp" ) ) (amount_pre + 1) dp_l)
  ** ((( &( "coins" ) )) # Ptr |-> (coins_pre))
  ** ((( &( "coinsSize" ) )) # Int |-> (coinsSize_pre))
  ** ((( &( "amount" ) )) # Int |-> (amount_pre))
  ** ((( &( "res" ) )) # Int |-> (res))
  ** (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
|--
  “ ((res - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (res - 1)) ”

noncomputable def coinChange_entail_wit_1 : Prop :=
  (
forall (coins_l : (List Int)) (coins_pre : Int) (coinsSize_pre : Int) (amount_pre : Int) (PreH1 : ((0 : Int) <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : ((0 : Int) <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH6 : (Forall ((GE.ge (α := Int)) (INT_MAX)) coins_l)) ,
  (((( &( "dp" ) ) + ((0 : Int) * sizeof(INT)))) # Int |-> (1))
  ** (intArray.undef_seg ( &( "dp" ) ) 1 100001)
  ** (intArray.full coins_pre coinsSize_pre coins_l)
|--
  EX dp_l : (List Int),
  “ ((0 : Int) <= coinsSize_pre) ” &&
  “ (coinsSize_pre <= 100000) ” &&
  “ (amount_pre <= 100000) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= (amount_pre + 1)) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) coins_l) ” &&
  “ (DpPrefixZeroed dp_l 1) ”
  &&  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) 1 dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) 1 (amount_pre + 1))
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
) \/
(
forall (coins_l : (List Int)) (coinsSize_pre : Int) (amount_pre : Int) (PreH1 : (1 <= INT_MAX)) (PreH2 : (1 >= INT_MIN)) (PreH3 : ((0 : Int) <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : ((0 : Int) <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH8 : (Forall ((GE.ge (α := Int)) (INT_MAX)) coins_l)) ,
  (((( &( "dp" ) ) + ((0 : Int) * sizeof(INT)))) # Int |-> (1))
|--
  EX dp_l : (List Int),
  “ ((0 : Int) <= coinsSize_pre) ” &&
  “ (coinsSize_pre <= 100000) ” &&
  “ (amount_pre <= 100000) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= (amount_pre + 1)) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) coins_l) ” &&
  “ (DpPrefixZeroed dp_l 1) ”
  &&  (intArray.seg ( &( "dp" ) ) (0 : Int) 1 dp_l)
)

noncomputable def coinChange_entail_wit_2 : Prop :=
  (
forall (coins_l : (List Int)) (coins_pre : Int) (coinsSize_pre : Int) (amount_pre : Int) (dp_l_2 : (List Int)) (j : Int) (PreH1 : (j <= amount_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (1 <= j)) (PreH6 : (j <= (amount_pre + 1))) (PreH7 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH8 : (DpPrefixZeroed dp_l_2 j)) ,
  (intArray.seg ( &( "dp" ) ) (0 : Int) (j + 1) (dp_l_2 ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "dp" ) ) (j + 1) (amount_pre + 1))
  ** (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
|--
  EX dp_l : (List Int),
  “ ((0 : Int) <= coinsSize_pre) ” &&
  “ (coinsSize_pre <= 100000) ” &&
  “ (amount_pre <= 100000) ” &&
  “ (1 <= (j + 1)) ” &&
  “ ((j + 1) <= (amount_pre + 1)) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) coins_l) ” &&
  “ (DpPrefixZeroed dp_l (j + 1)) ”
  &&  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) (j + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (j + 1) (amount_pre + 1))
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
) \/
(
forall (coins_l : (List Int)) (coinsSize_pre : Int) (amount_pre : Int) (dp_l_2 : (List Int)) (j : Int) (PreH1 : (j <= amount_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (1 <= j)) (PreH6 : (j <= (amount_pre + 1))) (PreH7 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH8 : (DpPrefixZeroed dp_l_2 j)) ,
  TT && emp 
|--
  “ (DpPrefixZeroed (dp_l_2 ++ ((0 : Int) :: (@List.nil Int))) (j + 1)) ”
  &&  emp
)

noncomputable def coinChange_entail_wit_2_split_goal_1 : Prop :=
  forall (coins_l : (List Int)) (coinsSize_pre : Int) (amount_pre : Int) (dp_l_2 : (List Int)) (j : Int) (PreH1 : (j <= amount_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (1 <= j)) (PreH6 : (j <= (amount_pre + 1))) (PreH7 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH8 : (DpPrefixZeroed dp_l_2 j)) ,
  (DpPrefixZeroed (dp_l_2 ++ ((0 : Int) :: (@List.nil Int))) (j + 1))

noncomputable def coinChange_entail_wit_3 : Prop :=
  (
forall (coins_l : (List Int)) (coins_pre : Int) (coinsSize_pre : Int) (amount_pre : Int) (dp_l_2 : (List Int)) (j : Int) (PreH1 : (j > amount_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (1 <= j)) (PreH6 : (j <= (amount_pre + 1))) (PreH7 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH8 : (DpPrefixZeroed dp_l_2 j)) ,
  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) j dp_l_2)
  ** (intArray.undef_seg ( &( "dp" ) ) j (amount_pre + 1))
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
|--
  EX dp_l : (List Int),
  “ (coinsSize_pre <= 100000) ” &&
  “ ((0 : Int) <= amount_pre) ” &&
  “ (amount_pre <= 100000) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= coinsSize_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) coins_l) ” &&
  “ (DpReachableTable (sublist ((0 : Int)) ((0 : Int)) (coins_l)) dp_l (amount_pre + 1)) ”
  &&  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full ( &( "dp" ) ) (amount_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
) \/
(
forall (coins_l : (List Int)) (coinsSize_pre : Int) (amount_pre : Int) (dp_l_2 : (List Int)) (j : Int) (PreH1 : (j > amount_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (1 <= j)) (PreH6 : (j <= (amount_pre + 1))) (PreH7 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH8 : (DpPrefixZeroed dp_l_2 j)) ,
  TT && emp 
|--
  “ (DpReachableTable (sublist ((0 : Int)) ((0 : Int)) (coins_l)) dp_l_2 (amount_pre + 1)) ”
  &&  emp
)

noncomputable def coinChange_entail_wit_3_split_goal_1 : Prop :=
  forall (coins_l : (List Int)) (coinsSize_pre : Int) (amount_pre : Int) (dp_l_2 : (List Int)) (j : Int) (PreH1 : (j > amount_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (1 <= j)) (PreH6 : (j <= (amount_pre + 1))) (PreH7 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH8 : (DpPrefixZeroed dp_l_2 j)) ,
  (DpReachableTable (sublist ((0 : Int)) ((0 : Int)) (coins_l)) dp_l_2 (amount_pre + 1))

noncomputable def coinChange_entail_wit_4 : Prop :=
  (
forall (coins_l : (List Int)) (coins_pre : Int) (coinsSize_pre : Int) (amount_pre : Int) (dp_l_2 : (List Int)) (i : Int) (PreH1 : ((Znth i coins_l (0 : Int)) <= amount_pre)) (PreH2 : (i < coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= coinsSize_pre)) (PreH8 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH9 : (DpReachableTable (sublist ((0 : Int)) (i) (coins_l)) dp_l_2 (amount_pre + 1))) ,
  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full ( &( "dp" ) ) (amount_pre + 1) dp_l_2)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
|--
  EX dp_l : (List Int),
  “ (coinsSize_pre <= 100000) ” &&
  “ (amount_pre <= 100000) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < coinsSize_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) coins_l) ” &&
  “ ((Znth i coins_l (0 : Int)) = (Znth i coins_l (0 : Int))) ” &&
  “ (1 <= (Znth i coins_l (0 : Int))) ” &&
  “ ((Znth i coins_l (0 : Int)) <= amount_pre) ” &&
  “ ((Znth i coins_l (0 : Int)) <= (Znth i coins_l (0 : Int))) ” &&
  “ ((Znth i coins_l (0 : Int)) <= (amount_pre + 1)) ” &&
  “ (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) (Znth i coins_l (0 : Int)) dp_l (Znth i coins_l (0 : Int)) amount_pre) ”
  &&  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full ( &( "dp" ) ) (amount_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
) \/
(
forall (coins_l : (List Int)) (coinsSize_pre : Int) (amount_pre : Int) (dp_l_2 : (List Int)) (i : Int) (PreH1 : ((Znth i coins_l (0 : Int)) <= amount_pre)) (PreH2 : (i < coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= coinsSize_pre)) (PreH8 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH9 : (DpReachableTable (sublist ((0 : Int)) (i) (coins_l)) dp_l_2 (amount_pre + 1))) ,
  TT && emp 
|--
  “ (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) (Znth i coins_l (0 : Int)) dp_l_2 (Znth i coins_l (0 : Int)) amount_pre) ” &&
  “ (1 <= (Znth i coins_l (0 : Int))) ”
  &&  emp
)

noncomputable def coinChange_entail_wit_4_split_goal_1 : Prop :=
  forall (coins_l : (List Int)) (coinsSize_pre : Int) (amount_pre : Int) (dp_l_2 : (List Int)) (i : Int) (PreH1 : ((Znth i coins_l (0 : Int)) <= amount_pre)) (PreH2 : (i < coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= coinsSize_pre)) (PreH8 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH9 : (DpReachableTable (sublist ((0 : Int)) (i) (coins_l)) dp_l_2 (amount_pre + 1))) ,
  (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) (Znth i coins_l (0 : Int)) dp_l_2 (Znth i coins_l (0 : Int)) amount_pre)

noncomputable def coinChange_entail_wit_4_split_goal_2 : Prop :=
  forall (coins_l : (List Int)) (coinsSize_pre : Int) (amount_pre : Int) (dp_l_2 : (List Int)) (i : Int) (PreH1 : ((Znth i coins_l (0 : Int)) <= amount_pre)) (PreH2 : (i < coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= coinsSize_pre)) (PreH8 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH9 : (DpReachableTable (sublist ((0 : Int)) (i) (coins_l)) dp_l_2 (amount_pre + 1))) ,
  (1 <= (Znth i coins_l (0 : Int)))

noncomputable def coinChange_entail_wit_5_1 : Prop :=
  (
forall (coins_l : (List Int)) (coins_pre : Int) (coinsSize_pre : Int) (amount_pre : Int) (dp_l_2 : (List Int)) (j : Int) (coin : Int) (i : Int) (PreH1 : ((Znth (j - coin) dp_l_2 (0 : Int)) ≠ (0 : Int))) (PreH2 : (j <= amount_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < coinsSize_pre)) (PreH7 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH8 : (coin = (Znth i coins_l (0 : Int)))) (PreH9 : (1 <= coin)) (PreH10 : (coin <= amount_pre)) (PreH11 : (coin <= j)) (PreH12 : (j <= (amount_pre + 1))) (PreH13 : (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l_2 j amount_pre)) ,
  (intArray.full ( &( "dp" ) ) (amount_pre + 1) (replace_Znth (j) (1) (dp_l_2)))
  ** (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
|--
  EX dp_l : (List Int),
  “ (coinsSize_pre <= 100000) ” &&
  “ (amount_pre <= 100000) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < coinsSize_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) coins_l) ” &&
  “ (coin = (Znth i coins_l (0 : Int))) ” &&
  “ (1 <= coin) ” &&
  “ (coin <= amount_pre) ” &&
  “ (coin <= (j + 1)) ” &&
  “ ((j + 1) <= (amount_pre + 1)) ” &&
  “ (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l (j + 1) amount_pre) ”
  &&  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full ( &( "dp" ) ) (amount_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
) \/
(
forall (coins_l : (List Int)) (coinsSize_pre : Int) (amount_pre : Int) (dp_l_2 : (List Int)) (j : Int) (coin : Int) (i : Int) (PreH1 : ((Znth (j - coin) dp_l_2 (0 : Int)) ≠ (0 : Int))) (PreH2 : (j <= amount_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < coinsSize_pre)) (PreH7 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH8 : (coin = (Znth i coins_l (0 : Int)))) (PreH9 : (1 <= coin)) (PreH10 : (coin <= amount_pre)) (PreH11 : (coin <= j)) (PreH12 : (j <= (amount_pre + 1))) (PreH13 : (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l_2 j amount_pre)) ,
  TT && emp 
|--
  “ (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin (replace_Znth (j) (1) (dp_l_2)) (j + 1) amount_pre) ”
  &&  emp
)

noncomputable def coinChange_entail_wit_5_1_split_goal_1 : Prop :=
  forall (coins_l : (List Int)) (coinsSize_pre : Int) (amount_pre : Int) (dp_l_2 : (List Int)) (j : Int) (coin : Int) (i : Int) (PreH1 : ((Znth (j - coin) dp_l_2 (0 : Int)) ≠ (0 : Int))) (PreH2 : (j <= amount_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < coinsSize_pre)) (PreH7 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH8 : (coin = (Znth i coins_l (0 : Int)))) (PreH9 : (1 <= coin)) (PreH10 : (coin <= amount_pre)) (PreH11 : (coin <= j)) (PreH12 : (j <= (amount_pre + 1))) (PreH13 : (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l_2 j amount_pre)) ,
  (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin (replace_Znth (j) (1) (dp_l_2)) (j + 1) amount_pre)

noncomputable def coinChange_entail_wit_5_2 : Prop :=
  (
forall (coins_l : (List Int)) (coins_pre : Int) (coinsSize_pre : Int) (amount_pre : Int) (dp_l_2 : (List Int)) (j : Int) (coin : Int) (i : Int) (PreH1 : ((Znth (j - coin) dp_l_2 (0 : Int)) = (0 : Int))) (PreH2 : (j <= amount_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < coinsSize_pre)) (PreH7 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH8 : (coin = (Znth i coins_l (0 : Int)))) (PreH9 : (1 <= coin)) (PreH10 : (coin <= amount_pre)) (PreH11 : (coin <= j)) (PreH12 : (j <= (amount_pre + 1))) (PreH13 : (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l_2 j amount_pre)) ,
  (intArray.full ( &( "dp" ) ) (amount_pre + 1) dp_l_2)
  ** (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
|--
  EX dp_l : (List Int),
  “ (coinsSize_pre <= 100000) ” &&
  “ (amount_pre <= 100000) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < coinsSize_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) coins_l) ” &&
  “ (coin = (Znth i coins_l (0 : Int))) ” &&
  “ (1 <= coin) ” &&
  “ (coin <= amount_pre) ” &&
  “ (coin <= (j + 1)) ” &&
  “ ((j + 1) <= (amount_pre + 1)) ” &&
  “ (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l (j + 1) amount_pre) ”
  &&  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full ( &( "dp" ) ) (amount_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
) \/
(
forall (coins_l : (List Int)) (coinsSize_pre : Int) (amount_pre : Int) (dp_l_2 : (List Int)) (j : Int) (coin : Int) (i : Int) (PreH1 : ((Znth (j - coin) dp_l_2 (0 : Int)) = (0 : Int))) (PreH2 : (j <= amount_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < coinsSize_pre)) (PreH7 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH8 : (coin = (Znth i coins_l (0 : Int)))) (PreH9 : (1 <= coin)) (PreH10 : (coin <= amount_pre)) (PreH11 : (coin <= j)) (PreH12 : (j <= (amount_pre + 1))) (PreH13 : (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l_2 j amount_pre)) ,
  TT && emp 
|--
  “ (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l_2 (j + 1) amount_pre) ”
  &&  emp
)

noncomputable def coinChange_entail_wit_5_2_split_goal_1 : Prop :=
  forall (coins_l : (List Int)) (coinsSize_pre : Int) (amount_pre : Int) (dp_l_2 : (List Int)) (j : Int) (coin : Int) (i : Int) (PreH1 : ((Znth (j - coin) dp_l_2 (0 : Int)) = (0 : Int))) (PreH2 : (j <= amount_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < coinsSize_pre)) (PreH7 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH8 : (coin = (Znth i coins_l (0 : Int)))) (PreH9 : (1 <= coin)) (PreH10 : (coin <= amount_pre)) (PreH11 : (coin <= j)) (PreH12 : (j <= (amount_pre + 1))) (PreH13 : (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l_2 j amount_pre)) ,
  (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l_2 (j + 1) amount_pre)

noncomputable def coinChange_entail_wit_6_1 : Prop :=
  (
forall (coins_l : (List Int)) (coins_pre : Int) (coinsSize_pre : Int) (amount_pre : Int) (dp_l_2 : (List Int)) (j : Int) (coin : Int) (i : Int) (PreH1 : (j > amount_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (amount_pre <= 100000)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < coinsSize_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH7 : (coin = (Znth i coins_l (0 : Int)))) (PreH8 : (1 <= coin)) (PreH9 : (coin <= amount_pre)) (PreH10 : (coin <= j)) (PreH11 : (j <= (amount_pre + 1))) (PreH12 : (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l_2 j amount_pre)) ,
  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full ( &( "dp" ) ) (amount_pre + 1) dp_l_2)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
|--
  EX dp_l : (List Int),
  “ (coinsSize_pre <= 100000) ” &&
  “ ((0 : Int) <= amount_pre) ” &&
  “ (amount_pre <= 100000) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= coinsSize_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) coins_l) ” &&
  “ (DpReachableTable (sublist ((0 : Int)) ((i + 1)) (coins_l)) dp_l (amount_pre + 1)) ”
  &&  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full ( &( "dp" ) ) (amount_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
) \/
(
forall (coins_l : (List Int)) (coinsSize_pre : Int) (amount_pre : Int) (dp_l_2 : (List Int)) (j : Int) (coin : Int) (i : Int) (PreH1 : (j > amount_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (amount_pre <= 100000)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < coinsSize_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH7 : (coin = (Znth i coins_l (0 : Int)))) (PreH8 : (1 <= coin)) (PreH9 : (coin <= amount_pre)) (PreH10 : (coin <= j)) (PreH11 : (j <= (amount_pre + 1))) (PreH12 : (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l_2 j amount_pre)) ,
  TT && emp 
|--
  “ (DpReachableTable (sublist ((0 : Int)) ((i + 1)) (coins_l)) dp_l_2 (amount_pre + 1)) ”
  &&  emp
)

noncomputable def coinChange_entail_wit_6_1_split_goal_1 : Prop :=
  forall (coins_l : (List Int)) (coinsSize_pre : Int) (amount_pre : Int) (dp_l_2 : (List Int)) (j : Int) (coin : Int) (i : Int) (PreH1 : (j > amount_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (amount_pre <= 100000)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < coinsSize_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH7 : (coin = (Znth i coins_l (0 : Int)))) (PreH8 : (1 <= coin)) (PreH9 : (coin <= amount_pre)) (PreH10 : (coin <= j)) (PreH11 : (j <= (amount_pre + 1))) (PreH12 : (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l_2 j amount_pre)) ,
  (DpReachableTable (sublist ((0 : Int)) ((i + 1)) (coins_l)) dp_l_2 (amount_pre + 1))

noncomputable def coinChange_entail_wit_6_2 : Prop :=
  (
forall (coins_l : (List Int)) (coins_pre : Int) (coinsSize_pre : Int) (amount_pre : Int) (dp_l_2 : (List Int)) (i : Int) (PreH1 : ((Znth i coins_l (0 : Int)) > amount_pre)) (PreH2 : (i < coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= coinsSize_pre)) (PreH8 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH9 : (DpReachableTable (sublist ((0 : Int)) (i) (coins_l)) dp_l_2 (amount_pre + 1))) ,
  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full ( &( "dp" ) ) (amount_pre + 1) dp_l_2)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
|--
  EX dp_l : (List Int),
  “ (coinsSize_pre <= 100000) ” &&
  “ ((0 : Int) <= amount_pre) ” &&
  “ (amount_pre <= 100000) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= coinsSize_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) coins_l) ” &&
  “ (DpReachableTable (sublist ((0 : Int)) ((i + 1)) (coins_l)) dp_l (amount_pre + 1)) ”
  &&  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full ( &( "dp" ) ) (amount_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
) \/
(
forall (coins_l : (List Int)) (coinsSize_pre : Int) (amount_pre : Int) (dp_l_2 : (List Int)) (i : Int) (PreH1 : ((Znth i coins_l (0 : Int)) > amount_pre)) (PreH2 : (i < coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= coinsSize_pre)) (PreH8 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH9 : (DpReachableTable (sublist ((0 : Int)) (i) (coins_l)) dp_l_2 (amount_pre + 1))) ,
  TT && emp 
|--
  “ (DpReachableTable (sublist ((0 : Int)) ((i + 1)) (coins_l)) dp_l_2 (amount_pre + 1)) ”
  &&  emp
)

noncomputable def coinChange_entail_wit_6_2_split_goal_1 : Prop :=
  forall (coins_l : (List Int)) (coinsSize_pre : Int) (amount_pre : Int) (dp_l_2 : (List Int)) (i : Int) (PreH1 : ((Znth i coins_l (0 : Int)) > amount_pre)) (PreH2 : (i < coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : ((0 : Int) <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= coinsSize_pre)) (PreH8 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH9 : (DpReachableTable (sublist ((0 : Int)) (i) (coins_l)) dp_l_2 (amount_pre + 1))) ,
  (DpReachableTable (sublist ((0 : Int)) ((i + 1)) (coins_l)) dp_l_2 (amount_pre + 1))

noncomputable def coinChange_entail_wit_7 : Prop :=
  (
forall (coins_l : (List Int)) (coins_pre : Int) (coinsSize_pre : Int) (amount_pre : Int) (dp_l_2 : (List Int)) (i : Int) (PreH1 : (i >= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : ((0 : Int) <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= coinsSize_pre)) (PreH7 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH8 : (DpReachableTable (sublist ((0 : Int)) (i) (coins_l)) dp_l_2 (amount_pre + 1))) ,
  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full ( &( "dp" ) ) (amount_pre + 1) dp_l_2)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
|--
  EX dp_l : (List Int),
  “ ((0 : Int) <= amount_pre) ” &&
  “ (amount_pre <= amount_pre) ” &&
  “ (DpReachableTable coins_l dp_l (amount_pre + 1)) ” &&
  “ (NoReachableAbove coins_l amount_pre amount_pre) ”
  &&  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full ( &( "dp" ) ) (amount_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
) \/
(
forall (coins_l : (List Int)) (coinsSize_pre : Int) (amount_pre : Int) (dp_l_2 : (List Int)) (i : Int) (PreH1 : (i >= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : ((0 : Int) <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= coinsSize_pre)) (PreH7 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH8 : (DpReachableTable (sublist ((0 : Int)) (i) (coins_l)) dp_l_2 (amount_pre + 1))) ,
  TT && emp 
|--
  “ (NoReachableAbove coins_l amount_pre amount_pre) ” &&
  “ (DpReachableTable coins_l dp_l_2 (amount_pre + 1)) ”
  &&  emp
)

noncomputable def coinChange_entail_wit_7_split_goal_1 : Prop :=
  forall (coins_l : (List Int)) (coinsSize_pre : Int) (amount_pre : Int) (dp_l_2 : (List Int)) (i : Int) (PreH1 : (i >= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : ((0 : Int) <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= coinsSize_pre)) (PreH7 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH8 : (DpReachableTable (sublist ((0 : Int)) (i) (coins_l)) dp_l_2 (amount_pre + 1))) ,
  (NoReachableAbove coins_l amount_pre amount_pre)

noncomputable def coinChange_entail_wit_7_split_goal_2 : Prop :=
  forall (coins_l : (List Int)) (coinsSize_pre : Int) (amount_pre : Int) (dp_l_2 : (List Int)) (i : Int) (PreH1 : (i >= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : ((0 : Int) <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= coinsSize_pre)) (PreH7 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH8 : (DpReachableTable (sublist ((0 : Int)) (i) (coins_l)) dp_l_2 (amount_pre + 1))) ,
  (DpReachableTable coins_l dp_l_2 (amount_pre + 1))

noncomputable def coinChange_entail_wit_8 : Prop :=
  (
forall (coins_l : (List Int)) (coins_pre : Int) (coinsSize_pre : Int) (amount_pre : Int) (dp_l_2 : (List Int)) (res : Int) (PreH1 : ((Znth res dp_l_2 (0 : Int)) = (0 : Int))) (PreH2 : (res > (0 : Int))) (PreH3 : ((0 : Int) <= res)) (PreH4 : (res <= amount_pre)) (PreH5 : (DpReachableTable coins_l dp_l_2 (amount_pre + 1))) (PreH6 : (NoReachableAbove coins_l amount_pre res)) ,
  (intArray.full ( &( "dp" ) ) (amount_pre + 1) dp_l_2)
  ** (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
|--
  EX dp_l : (List Int),
  “ ((0 : Int) <= (res - 1)) ” &&
  “ ((res - 1) <= amount_pre) ” &&
  “ (DpReachableTable coins_l dp_l (amount_pre + 1)) ” &&
  “ (NoReachableAbove coins_l amount_pre (res - 1)) ”
  &&  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full ( &( "dp" ) ) (amount_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
) \/
(
forall (coins_l : (List Int)) (amount_pre : Int) (dp_l_2 : (List Int)) (res : Int) (PreH1 : ((Znth res dp_l_2 (0 : Int)) = (0 : Int))) (PreH2 : (res > (0 : Int))) (PreH3 : ((0 : Int) <= res)) (PreH4 : (res <= amount_pre)) (PreH5 : (DpReachableTable coins_l dp_l_2 (amount_pre + 1))) (PreH6 : (NoReachableAbove coins_l amount_pre res)) ,
  TT && emp 
|--
  “ (NoReachableAbove coins_l amount_pre (res - 1)) ”
  &&  emp
)

noncomputable def coinChange_entail_wit_8_split_goal_1 : Prop :=
  forall (coins_l : (List Int)) (amount_pre : Int) (dp_l_2 : (List Int)) (res : Int) (PreH1 : ((Znth res dp_l_2 (0 : Int)) = (0 : Int))) (PreH2 : (res > (0 : Int))) (PreH3 : ((0 : Int) <= res)) (PreH4 : (res <= amount_pre)) (PreH5 : (DpReachableTable coins_l dp_l_2 (amount_pre + 1))) (PreH6 : (NoReachableAbove coins_l amount_pre res)) ,
  (NoReachableAbove coins_l amount_pre (res - 1))

noncomputable def coinChange_entail_wit_9_1 : Prop :=
  (
forall (coins_l : (List Int)) (coins_pre : Int) (coinsSize_pre : Int) (amount_pre : Int) (dp_l : (List Int)) (res : Int) (PreH1 : (res <= (0 : Int))) (PreH2 : ((0 : Int) <= res)) (PreH3 : (res <= amount_pre)) (PreH4 : (DpReachableTable coins_l dp_l (amount_pre + 1))) (PreH5 : (NoReachableAbove coins_l amount_pre res)) ,
  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full ( &( "dp" ) ) (amount_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
|--
  “ (MaxReachableAmount coins_l amount_pre res) ”
  &&  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.undef_full ( &( "dp" ) ) 100001)
) \/
(
forall (coins_l : (List Int)) (amount_pre : Int) (dp_l : (List Int)) (res : Int) (PreH1 : (res <= (0 : Int))) (PreH2 : ((0 : Int) <= res)) (PreH3 : (res <= amount_pre)) (PreH4 : (DpReachableTable coins_l dp_l (amount_pre + 1))) (PreH5 : (NoReachableAbove coins_l amount_pre res)) ,
  (intArray.full ( &( "dp" ) ) (amount_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
|--
  “ (MaxReachableAmount coins_l amount_pre res) ”
  &&  (intArray.undef_full ( &( "dp" ) ) 100001)
)

noncomputable def coinChange_entail_wit_9_1_split_goal_1 : Prop :=
  forall (coins_l : (List Int)) (amount_pre : Int) (dp_l : (List Int)) (res : Int) (PreH1 : (res <= (0 : Int))) (PreH2 : ((0 : Int) <= res)) (PreH3 : (res <= amount_pre)) (PreH4 : (DpReachableTable coins_l dp_l (amount_pre + 1))) (PreH5 : (NoReachableAbove coins_l amount_pre res)) ,
  (intArray.full ( &( "dp" ) ) (amount_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
|--
  “ (MaxReachableAmount coins_l amount_pre res) ”

noncomputable def coinChange_entail_wit_9_1_split_goal_spatial : Prop :=
  forall (coins_l : (List Int)) (amount_pre : Int) (dp_l : (List Int)) (res : Int) (PreH1 : (res <= (0 : Int))) (PreH2 : ((0 : Int) <= res)) (PreH3 : (res <= amount_pre)) (PreH4 : (DpReachableTable coins_l dp_l (amount_pre + 1))) (PreH5 : (NoReachableAbove coins_l amount_pre res)) ,
  (intArray.full ( &( "dp" ) ) (amount_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
|--
  (intArray.undef_full ( &( "dp" ) ) 100001)

noncomputable def coinChange_entail_wit_9_2 : Prop :=
  (
forall (coins_l : (List Int)) (coins_pre : Int) (coinsSize_pre : Int) (amount_pre : Int) (dp_l : (List Int)) (res : Int) (PreH1 : ((Znth res dp_l (0 : Int)) ≠ (0 : Int))) (PreH2 : (res > (0 : Int))) (PreH3 : ((0 : Int) <= res)) (PreH4 : (res <= amount_pre)) (PreH5 : (DpReachableTable coins_l dp_l (amount_pre + 1))) (PreH6 : (NoReachableAbove coins_l amount_pre res)) ,
  (intArray.full ( &( "dp" ) ) (amount_pre + 1) dp_l)
  ** (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
|--
  “ (MaxReachableAmount coins_l amount_pre res) ”
  &&  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.undef_full ( &( "dp" ) ) 100001)
) \/
(
forall (coins_l : (List Int)) (amount_pre : Int) (dp_l : (List Int)) (res : Int) (PreH1 : ((Znth res dp_l (0 : Int)) ≠ (0 : Int))) (PreH2 : (res > (0 : Int))) (PreH3 : ((0 : Int) <= res)) (PreH4 : (res <= amount_pre)) (PreH5 : (DpReachableTable coins_l dp_l (amount_pre + 1))) (PreH6 : (NoReachableAbove coins_l amount_pre res)) ,
  (intArray.full ( &( "dp" ) ) (amount_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
|--
  “ (MaxReachableAmount coins_l amount_pre res) ”
  &&  (intArray.undef_full ( &( "dp" ) ) 100001)
)

noncomputable def coinChange_entail_wit_9_2_split_goal_1 : Prop :=
  forall (coins_l : (List Int)) (amount_pre : Int) (dp_l : (List Int)) (res : Int) (PreH1 : ((Znth res dp_l (0 : Int)) ≠ (0 : Int))) (PreH2 : (res > (0 : Int))) (PreH3 : ((0 : Int) <= res)) (PreH4 : (res <= amount_pre)) (PreH5 : (DpReachableTable coins_l dp_l (amount_pre + 1))) (PreH6 : (NoReachableAbove coins_l amount_pre res)) ,
  (intArray.full ( &( "dp" ) ) (amount_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
|--
  “ (MaxReachableAmount coins_l amount_pre res) ”

noncomputable def coinChange_entail_wit_9_2_split_goal_spatial : Prop :=
  forall (coins_l : (List Int)) (amount_pre : Int) (dp_l : (List Int)) (res : Int) (PreH1 : ((Znth res dp_l (0 : Int)) ≠ (0 : Int))) (PreH2 : (res > (0 : Int))) (PreH3 : ((0 : Int) <= res)) (PreH4 : (res <= amount_pre)) (PreH5 : (DpReachableTable coins_l dp_l (amount_pre + 1))) (PreH6 : (NoReachableAbove coins_l amount_pre res)) ,
  (intArray.full ( &( "dp" ) ) (amount_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
|--
  (intArray.undef_full ( &( "dp" ) ) 100001)

noncomputable def coinChange_return_wit_1 : Prop :=
  forall (coins_l : (List Int)) (coins_pre : Int) (coinsSize_pre : Int) (amount_pre : Int) (res : Int) (PreH1 : (MaxReachableAmount coins_l amount_pre res)) ,
  (intArray.full coins_pre coinsSize_pre coins_l)
|--
  “ (MaxReachableAmount coins_l amount_pre res) ”
  &&  (intArray.full coins_pre coinsSize_pre coins_l)

noncomputable def coinChange_partial_solve_wit_1 : Prop :=
  forall (coins_l : (List Int)) (coins_pre : Int) (coinsSize_pre : Int) (amount_pre : Int) (PreH1 : ((0 : Int) <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : ((0 : Int) <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH6 : (Forall ((GE.ge (α := Int)) (INT_MAX)) coins_l)) ,
  (intArray.undef_full ( &( "dp" ) ) 100001)
  ** (intArray.full coins_pre coinsSize_pre coins_l)
|--
  “ ((0 : Int) <= coinsSize_pre) ” &&
  “ (coinsSize_pre <= 100000) ” &&
  “ ((0 : Int) <= amount_pre) ” &&
  “ (amount_pre <= 100000) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) coins_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (INT_MAX)) coins_l) ”
  &&  (((( &( "dp" ) ) + ((0 : Int) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg ( &( "dp" ) ) 1 100001)
  ** (intArray.full coins_pre coinsSize_pre coins_l)

noncomputable def coinChange_partial_solve_wit_2 : Prop :=
  forall (coins_l : (List Int)) (coins_pre : Int) (coinsSize_pre : Int) (amount_pre : Int) (dp_l : (List Int)) (j : Int) (PreH1 : (j <= amount_pre)) (PreH2 : ((0 : Int) <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (1 <= j)) (PreH6 : (j <= (amount_pre + 1))) (PreH7 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH8 : (DpPrefixZeroed dp_l j)) ,
  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) j dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) j (amount_pre + 1))
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
|--
  “ (j <= amount_pre) ” &&
  “ ((0 : Int) <= coinsSize_pre) ” &&
  “ (coinsSize_pre <= 100000) ” &&
  “ (amount_pre <= 100000) ” &&
  “ (1 <= j) ” &&
  “ (j <= (amount_pre + 1)) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) coins_l) ” &&
  “ (DpPrefixZeroed dp_l j) ”
  &&  (((( &( "dp" ) ) + (j * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg ( &( "dp" ) ) (j + 1) (amount_pre + 1))
  ** (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) j dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)

noncomputable def coinChange_partial_solve_wit_3 : Prop :=
  forall (coins_l : (List Int)) (coins_pre : Int) (coinsSize_pre : Int) (amount_pre : Int) (dp_l : (List Int)) (i : Int) (PreH1 : (i < coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : ((0 : Int) <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= coinsSize_pre)) (PreH7 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH8 : (DpReachableTable (sublist ((0 : Int)) (i) (coins_l)) dp_l (amount_pre + 1))) ,
  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full ( &( "dp" ) ) (amount_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
|--
  “ (i < coinsSize_pre) ” &&
  “ (coinsSize_pre <= 100000) ” &&
  “ ((0 : Int) <= amount_pre) ” &&
  “ (amount_pre <= 100000) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= coinsSize_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) coins_l) ” &&
  “ (DpReachableTable (sublist ((0 : Int)) (i) (coins_l)) dp_l (amount_pre + 1)) ”
  &&  (((coins_pre + (i * sizeof(INT)))) # Int |-> ((Znth i coins_l (0 : Int))))
  ** (intArray.missing_i coins_pre i (0 : Int) coinsSize_pre coins_l)
  ** (intArray.full ( &( "dp" ) ) (amount_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)

noncomputable def coinChange_partial_solve_wit_4 : Prop :=
  forall (coins_l : (List Int)) (coins_pre : Int) (coinsSize_pre : Int) (amount_pre : Int) (dp_l : (List Int)) (j : Int) (coin : Int) (i : Int) (PreH1 : (j <= amount_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (amount_pre <= 100000)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i < coinsSize_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH7 : (coin = (Znth i coins_l (0 : Int)))) (PreH8 : (1 <= coin)) (PreH9 : (coin <= amount_pre)) (PreH10 : (coin <= j)) (PreH11 : (j <= (amount_pre + 1))) (PreH12 : (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l j amount_pre)) ,
  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full ( &( "dp" ) ) (amount_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
|--
  “ (j <= amount_pre) ” &&
  “ (coinsSize_pre <= 100000) ” &&
  “ (amount_pre <= 100000) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < coinsSize_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) coins_l) ” &&
  “ (coin = (Znth i coins_l (0 : Int))) ” &&
  “ (1 <= coin) ” &&
  “ (coin <= amount_pre) ” &&
  “ (coin <= j) ” &&
  “ (j <= (amount_pre + 1)) ” &&
  “ (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l j amount_pre) ”
  &&  (((( &( "dp" ) ) + ((j - coin) * sizeof(INT)))) # Int |-> ((Znth (j - coin) dp_l (0 : Int))))
  ** (intArray.missing_i ( &( "dp" ) ) (j - coin) (0 : Int) (amount_pre + 1) dp_l)
  ** (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)

noncomputable def coinChange_partial_solve_wit_5 : Prop :=
  forall (coins_l : (List Int)) (coins_pre : Int) (coinsSize_pre : Int) (amount_pre : Int) (dp_l : (List Int)) (j : Int) (coin : Int) (i : Int) (PreH1 : ((Znth (j - coin) dp_l (0 : Int)) ≠ (0 : Int))) (PreH2 : (j <= amount_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i < coinsSize_pre)) (PreH7 : (Forall ((LE.le (α := Int)) (1)) coins_l)) (PreH8 : (coin = (Znth i coins_l (0 : Int)))) (PreH9 : (1 <= coin)) (PreH10 : (coin <= amount_pre)) (PreH11 : (coin <= j)) (PreH12 : (j <= (amount_pre + 1))) (PreH13 : (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l j amount_pre)) ,
  (intArray.full ( &( "dp" ) ) (amount_pre + 1) dp_l)
  ** (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
|--
  “ ((Znth (j - coin) dp_l (0 : Int)) ≠ (0 : Int)) ” &&
  “ (j <= amount_pre) ” &&
  “ (coinsSize_pre <= 100000) ” &&
  “ (amount_pre <= 100000) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < coinsSize_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) coins_l) ” &&
  “ (coin = (Znth i coins_l (0 : Int))) ” &&
  “ (1 <= coin) ” &&
  “ (coin <= amount_pre) ” &&
  “ (coin <= j) ” &&
  “ (j <= (amount_pre + 1)) ” &&
  “ (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l j amount_pre) ”
  &&  (((( &( "dp" ) ) + (j * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i ( &( "dp" ) ) j (0 : Int) (amount_pre + 1) dp_l)
  ** (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)

noncomputable def coinChange_partial_solve_wit_6 : Prop :=
  forall (coins_l : (List Int)) (coins_pre : Int) (coinsSize_pre : Int) (amount_pre : Int) (dp_l : (List Int)) (res : Int) (PreH1 : (res > (0 : Int))) (PreH2 : ((0 : Int) <= res)) (PreH3 : (res <= amount_pre)) (PreH4 : (DpReachableTable coins_l dp_l (amount_pre + 1))) (PreH5 : (NoReachableAbove coins_l amount_pre res)) ,
  (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.full ( &( "dp" ) ) (amount_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)
|--
  “ (res > (0 : Int)) ” &&
  “ ((0 : Int) <= res) ” &&
  “ (res <= amount_pre) ” &&
  “ (DpReachableTable coins_l dp_l (amount_pre + 1)) ” &&
  “ (NoReachableAbove coins_l amount_pre res) ”
  &&  (((( &( "dp" ) ) + (res * sizeof(INT)))) # Int |-> ((Znth res dp_l (0 : Int))))
  ** (intArray.missing_i ( &( "dp" ) ) res (0 : Int) (amount_pre + 1) dp_l)
  ** (intArray.full coins_pre coinsSize_pre coins_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (amount_pre + 1) 100001)


structure VC_Correct : Type where
  proof_of_coinChange_safety_wit_1 : coinChange_safety_wit_1
  proof_of_coinChange_safety_wit_2 : coinChange_safety_wit_2
  proof_of_coinChange_safety_wit_3 : coinChange_safety_wit_3
  proof_of_coinChange_safety_wit_4 : coinChange_safety_wit_4
  proof_of_coinChange_safety_wit_5 : coinChange_safety_wit_5
  proof_of_coinChange_safety_wit_6 : coinChange_safety_wit_6
  proof_of_coinChange_safety_wit_7 : coinChange_safety_wit_7
  proof_of_coinChange_safety_wit_8 : coinChange_safety_wit_8
  proof_of_coinChange_safety_wit_9 : coinChange_safety_wit_9
  proof_of_coinChange_safety_wit_10 : coinChange_safety_wit_10
  proof_of_coinChange_safety_wit_11 : coinChange_safety_wit_11
  proof_of_coinChange_safety_wit_12 : coinChange_safety_wit_12
  proof_of_coinChange_safety_wit_13 : coinChange_safety_wit_13
  proof_of_coinChange_safety_wit_14 : coinChange_safety_wit_14
  proof_of_coinChange_safety_wit_15 : coinChange_safety_wit_15
  proof_of_coinChange_safety_wit_16 : coinChange_safety_wit_16
  proof_of_coinChange_return_wit_1 : coinChange_return_wit_1
  proof_of_coinChange_partial_solve_wit_1 : coinChange_partial_solve_wit_1
  proof_of_coinChange_partial_solve_wit_2 : coinChange_partial_solve_wit_2
  proof_of_coinChange_partial_solve_wit_3 : coinChange_partial_solve_wit_3
  proof_of_coinChange_partial_solve_wit_4 : coinChange_partial_solve_wit_4
  proof_of_coinChange_partial_solve_wit_5 : coinChange_partial_solve_wit_5
  proof_of_coinChange_partial_solve_wit_6 : coinChange_partial_solve_wit_6
  proof_of_coinChange_entail_wit_1 : coinChange_entail_wit_1
  proof_of_coinChange_entail_wit_2 : coinChange_entail_wit_2
  proof_of_coinChange_entail_wit_3 : coinChange_entail_wit_3
  proof_of_coinChange_entail_wit_4 : coinChange_entail_wit_4
  proof_of_coinChange_entail_wit_5_1 : coinChange_entail_wit_5_1
  proof_of_coinChange_entail_wit_5_2 : coinChange_entail_wit_5_2
  proof_of_coinChange_entail_wit_6_1 : coinChange_entail_wit_6_1
  proof_of_coinChange_entail_wit_6_2 : coinChange_entail_wit_6_2
  proof_of_coinChange_entail_wit_7 : coinChange_entail_wit_7
  proof_of_coinChange_entail_wit_8 : coinChange_entail_wit_8
  proof_of_coinChange_entail_wit_9_1 : coinChange_entail_wit_9_1
  proof_of_coinChange_entail_wit_9_2 : coinChange_entail_wit_9_2

end SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_goal
