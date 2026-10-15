import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.rod_cutting.rod_cutting_lib
open SimpleC.EE.LLM_bench.Algorithms.rod_cutting.rod_cutting_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.rod_cutting.rod_cutting_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance rod_cutting_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def rod_cutting_safety_wit_1 : Prop :=
  forall (n_pre : Int) (price_pre : Int) (price_l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (price_l)) = (n_pre + 1))) (PreH4 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH5 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH6 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) ,
  ((( &( "j" ) )) # Int |->_)
  ** (intArray.undef_full ( &( "revenue" ) ) 1001)
  ** ((( &( "price" ) )) # Ptr |-> (price_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full price_pre (n_pre + 1) price_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def rod_cutting_safety_wit_2 : Prop :=
  forall (n_pre : Int) (price_pre : Int) (price_l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (price_l)) = (n_pre + 1))) (PreH4 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH5 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH6 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) ,
  ((( &( "j" ) )) # Int |->_)
  ** (intArray.undef_full ( &( "revenue" ) ) 1001)
  ** ((( &( "price" ) )) # Ptr |-> (price_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full price_pre (n_pre + 1) price_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def rod_cutting_safety_wit_3 : Prop :=
  forall (n_pre : Int) (price_pre : Int) (price_l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (price_l)) = (n_pre + 1))) (PreH4 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH5 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH6 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) ,
  (((( &( "revenue" ) ) + ((0 : Int) * sizeof(INT)))) # Int |-> ((0 : Int)))
  ** (intArray.undef_seg ( &( "revenue" ) ) 1 1001)
  ** ((( &( "j" ) )) # Int |->_)
  ** ((( &( "price" ) )) # Ptr |-> (price_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full price_pre (n_pre + 1) price_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def rod_cutting_safety_wit_4 : Prop :=
  forall (n_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l : (List Int)) (j : Int) (PreH1 : (j <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) (PreH5 : (1 <= j)) (PreH6 : (j <= (n_pre + 1))) (PreH7 : (RodCutRevenueTable price_l revenue_l j)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < j)) -> (((0 : Int) <= (Znth k revenue_l (0 : Int))) ∧ ((Znth k revenue_l (0 : Int)) <= (k * 1000000))))) ,
  ((( &( "best" ) )) # Int |->_)
  ** ((( &( "price" ) )) # Ptr |-> (price_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.seg ( &( "revenue" ) ) (0 : Int) j revenue_l)
  ** (intArray.undef_seg ( &( "revenue" ) ) j 1001)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def rod_cutting_safety_wit_5 : Prop :=
  forall (n_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l : (List Int)) (j : Int) (PreH1 : (j <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) (PreH5 : (1 <= j)) (PreH6 : (j <= (n_pre + 1))) (PreH7 : (RodCutRevenueTable price_l revenue_l j)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < j)) -> (((0 : Int) <= (Znth k revenue_l (0 : Int))) ∧ ((Znth k revenue_l (0 : Int)) <= (k * 1000000))))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "best" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "price" ) )) # Ptr |-> (price_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.seg ( &( "revenue" ) ) (0 : Int) j revenue_l)
  ** (intArray.undef_seg ( &( "revenue" ) ) j 1001)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def rod_cutting_safety_wit_6 : Prop :=
  (
forall (n_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (i <= j)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) (PreH5 : (1 <= j)) (PreH6 : (j <= n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (j + 1))) (PreH9 : ((0 : Int) <= best)) (PreH10 : (best <= (j * 1000000))) (PreH11 : (RodCutRevenueTable price_l revenue_l j)) (PreH12 : (RodCutScanBest price_l revenue_l j i best)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < j)) -> (((0 : Int) <= (Znth k revenue_l (0 : Int))) ∧ ((Znth k revenue_l (0 : Int)) <= (k * 1000000))))) ,
  (intArray.seg ( &( "revenue" ) ) (0 : Int) j revenue_l)
  ** (intArray.full price_pre (n_pre + 1) price_l)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "price" ) )) # Ptr |-> (price_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.undef_seg ( &( "revenue" ) ) j 1001)
|--
  “ (((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l (0 : Int)))) ”
) \/
(
forall (n_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (i <= j)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) (PreH5 : (1 <= j)) (PreH6 : (j <= n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (j + 1))) (PreH9 : ((0 : Int) <= best)) (PreH10 : (best <= (j * 1000000))) (PreH11 : (RodCutRevenueTable price_l revenue_l j)) (PreH12 : (RodCutScanBest price_l revenue_l j i best)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < j)) -> (((0 : Int) <= (Znth k revenue_l (0 : Int))) ∧ ((Znth k revenue_l (0 : Int)) <= (k * 1000000))))) ,
  (intArray.seg ( &( "revenue" ) ) (0 : Int) j revenue_l)
  ** (intArray.full price_pre (n_pre + 1) price_l)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "price" ) )) # Ptr |-> (price_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.undef_seg ( &( "revenue" ) ) j 1001)
|--
  “ (((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l (0 : Int)))) ”
)

noncomputable def rod_cutting_safety_wit_6_split_goal_1 : Prop :=
  forall (n_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (i <= j)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) (PreH5 : (1 <= j)) (PreH6 : (j <= n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (j + 1))) (PreH9 : ((0 : Int) <= best)) (PreH10 : (best <= (j * 1000000))) (PreH11 : (RodCutRevenueTable price_l revenue_l j)) (PreH12 : (RodCutScanBest price_l revenue_l j i best)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < j)) -> (((0 : Int) <= (Znth k revenue_l (0 : Int))) ∧ ((Znth k revenue_l (0 : Int)) <= (k * 1000000))))) ,
  (intArray.seg ( &( "revenue" ) ) (0 : Int) j revenue_l)
  ** (intArray.full price_pre (n_pre + 1) price_l)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "price" ) )) # Ptr |-> (price_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.undef_seg ( &( "revenue" ) ) j 1001)
|--
  “ (((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l (0 : Int))) <= INT_MAX) ”

noncomputable def rod_cutting_safety_wit_6_split_goal_2 : Prop :=
  forall (n_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (i <= j)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) (PreH5 : (1 <= j)) (PreH6 : (j <= n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (j + 1))) (PreH9 : ((0 : Int) <= best)) (PreH10 : (best <= (j * 1000000))) (PreH11 : (RodCutRevenueTable price_l revenue_l j)) (PreH12 : (RodCutScanBest price_l revenue_l j i best)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < j)) -> (((0 : Int) <= (Znth k revenue_l (0 : Int))) ∧ ((Znth k revenue_l (0 : Int)) <= (k * 1000000))))) ,
  (intArray.seg ( &( "revenue" ) ) (0 : Int) j revenue_l)
  ** (intArray.full price_pre (n_pre + 1) price_l)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "price" ) )) # Ptr |-> (price_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.undef_seg ( &( "revenue" ) ) j 1001)
|--
  “ ((INT_MIN) <= ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l (0 : Int)))) ”

noncomputable def rod_cutting_safety_wit_7 : Prop :=
  forall (n_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (i <= j)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) (PreH5 : (1 <= j)) (PreH6 : (j <= n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (j + 1))) (PreH9 : ((0 : Int) <= best)) (PreH10 : (best <= (j * 1000000))) (PreH11 : (RodCutRevenueTable price_l revenue_l j)) (PreH12 : (RodCutScanBest price_l revenue_l j i best)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < j)) -> (((0 : Int) <= (Znth k revenue_l (0 : Int))) ∧ ((Znth k revenue_l (0 : Int)) <= (k * 1000000))))) ,
  (intArray.full price_pre (n_pre + 1) price_l)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "price" ) )) # Ptr |-> (price_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.seg ( &( "revenue" ) ) (0 : Int) j revenue_l)
  ** (intArray.undef_seg ( &( "revenue" ) ) j 1001)
|--
  “ ((j - i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j - i)) ”

noncomputable def rod_cutting_safety_wit_8 : Prop :=
  forall (n_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (best < ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l (0 : Int))))) (PreH2 : (i <= j)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) (PreH6 : (1 <= j)) (PreH7 : (j <= n_pre)) (PreH8 : (1 <= i)) (PreH9 : (i <= (j + 1))) (PreH10 : ((0 : Int) <= best)) (PreH11 : (best <= (j * 1000000))) (PreH12 : (RodCutRevenueTable price_l revenue_l j)) (PreH13 : (RodCutScanBest price_l revenue_l j i best)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < j)) -> (((0 : Int) <= (Znth k revenue_l (0 : Int))) ∧ ((Znth k revenue_l (0 : Int)) <= (k * 1000000))))) ,
  (intArray.seg ( &( "revenue" ) ) (0 : Int) j revenue_l)
  ** (intArray.full price_pre (n_pre + 1) price_l)
  ** ((( &( "price" ) )) # Ptr |-> (price_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "best" ) )) # Int |-> (((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l (0 : Int)))))
  ** (intArray.undef_seg ( &( "revenue" ) ) j 1001)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def rod_cutting_safety_wit_9 : Prop :=
  forall (n_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (best >= ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l (0 : Int))))) (PreH2 : (i <= j)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) (PreH6 : (1 <= j)) (PreH7 : (j <= n_pre)) (PreH8 : (1 <= i)) (PreH9 : (i <= (j + 1))) (PreH10 : ((0 : Int) <= best)) (PreH11 : (best <= (j * 1000000))) (PreH12 : (RodCutRevenueTable price_l revenue_l j)) (PreH13 : (RodCutScanBest price_l revenue_l j i best)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < j)) -> (((0 : Int) <= (Znth k revenue_l (0 : Int))) ∧ ((Znth k revenue_l (0 : Int)) <= (k * 1000000))))) ,
  (intArray.seg ( &( "revenue" ) ) (0 : Int) j revenue_l)
  ** (intArray.full price_pre (n_pre + 1) price_l)
  ** ((( &( "price" ) )) # Ptr |-> (price_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.undef_seg ( &( "revenue" ) ) j 1001)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def rod_cutting_safety_wit_10 : Prop :=
  forall (n_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (i > j)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) (PreH5 : (1 <= j)) (PreH6 : (j <= n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (j + 1))) (PreH9 : ((0 : Int) <= best)) (PreH10 : (best <= (j * 1000000))) (PreH11 : (RodCutRevenueTable price_l revenue_l j)) (PreH12 : (RodCutScanBest price_l revenue_l j i best)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < j)) -> (((0 : Int) <= (Znth k revenue_l (0 : Int))) ∧ ((Znth k revenue_l (0 : Int)) <= (k * 1000000))))) ,
  (intArray.seg ( &( "revenue" ) ) (0 : Int) (j + 1) (revenue_l ++ (best :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "revenue" ) ) (j + 1) 1001)
  ** ((( &( "price" ) )) # Ptr |-> (price_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full price_pre (n_pre + 1) price_l)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def rod_cutting_entail_wit_1 : Prop :=
  (
forall (n_pre : Int) (price_pre : Int) (price_l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (price_l)) = (n_pre + 1))) (PreH4 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH5 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH6 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) ,
  (((( &( "revenue" ) ) + ((0 : Int) * sizeof(INT)))) # Int |-> ((0 : Int)))
  ** (intArray.undef_seg ( &( "revenue" ) ) 1 1001)
  ** (intArray.full price_pre (n_pre + 1) price_l)
|--
  EX revenue_l : (List Int),
  “ (n_pre <= 1000) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) price_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000000)) price_l) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= (n_pre + 1)) ” &&
  “ (RodCutRevenueTable price_l revenue_l 1) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < 1)) -> (((0 : Int) <= (Znth k revenue_l (0 : Int))) ∧ ((Znth k revenue_l (0 : Int)) <= (k * 1000000)))) ”
  &&  (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.seg ( &( "revenue" ) ) (0 : Int) 1 revenue_l)
  ** (intArray.undef_seg ( &( "revenue" ) ) 1 1001)
) \/
(
forall (n_pre : Int) (price_l : (List Int)) (PreH1 : ((0 : Int) <= INT_MAX)) (PreH2 : ((0 : Int) >= INT_MIN)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (price_l)) = (n_pre + 1))) (PreH6 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH8 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) ,
  (((( &( "revenue" ) ) + ((0 : Int) * sizeof(INT)))) # Int |-> ((0 : Int)))
|--
  EX revenue_l : (List Int),
  “ (n_pre <= 1000) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) price_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000000)) price_l) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= (n_pre + 1)) ” &&
  “ (RodCutRevenueTable price_l revenue_l 1) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < 1)) -> (((0 : Int) <= (Znth k revenue_l (0 : Int))) ∧ ((Znth k revenue_l (0 : Int)) <= (k * 1000000)))) ”
  &&  (intArray.seg ( &( "revenue" ) ) (0 : Int) 1 revenue_l)
)

noncomputable def rod_cutting_entail_wit_2 : Prop :=
  (
forall (n_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (j : Int) (PreH1 : (j <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) (PreH5 : (1 <= j)) (PreH6 : (j <= (n_pre + 1))) (PreH7 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l_2 (0 : Int))) ∧ ((Znth k_2 revenue_l_2 (0 : Int)) <= (k_2 * 1000000))))) ,
  (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.seg ( &( "revenue" ) ) (0 : Int) j revenue_l_2)
  ** (intArray.undef_seg ( &( "revenue" ) ) j 1001)
|--
  EX revenue_l : (List Int),
  “ (n_pre <= 1000) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) price_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000000)) price_l) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= (j + 1)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (j * 1000000)) ” &&
  “ (RodCutRevenueTable price_l revenue_l j) ” &&
  “ (RodCutScanBest price_l revenue_l j 1 (0 : Int)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < j)) -> (((0 : Int) <= (Znth k revenue_l (0 : Int))) ∧ ((Znth k revenue_l (0 : Int)) <= (k * 1000000)))) ”
  &&  (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.seg ( &( "revenue" ) ) (0 : Int) j revenue_l)
  ** (intArray.undef_seg ( &( "revenue" ) ) j 1001)
) \/
(
forall (n_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (j : Int) (PreH1 : (j <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) (PreH5 : (1 <= j)) (PreH6 : (j <= (n_pre + 1))) (PreH7 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l_2 (0 : Int))) ∧ ((Znth k_2 revenue_l_2 (0 : Int)) <= (k_2 * 1000000))))) ,
  TT && emp 
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < j)) -> (((0 : Int) <= (Znth k revenue_l_2 (0 : Int))) ∧ ((Znth k revenue_l_2 (0 : Int)) <= (k * 1000000)))) ” &&
  “ (RodCutScanBest price_l revenue_l_2 j 1 (0 : Int)) ”
  &&  emp
)

noncomputable def rod_cutting_entail_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (j : Int) (PreH1 : (j <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) (PreH5 : (1 <= j)) (PreH6 : (j <= (n_pre + 1))) (PreH7 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l_2 (0 : Int))) ∧ ((Znth k_2 revenue_l_2 (0 : Int)) <= (k_2 * 1000000))))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < j)) -> (((0 : Int) <= (Znth k revenue_l_2 (0 : Int))) ∧ ((Znth k revenue_l_2 (0 : Int)) <= (k * 1000000))))

noncomputable def rod_cutting_entail_wit_2_split_goal_2 : Prop :=
  forall (n_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (j : Int) (PreH1 : (j <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) (PreH5 : (1 <= j)) (PreH6 : (j <= (n_pre + 1))) (PreH7 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH8 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l_2 (0 : Int))) ∧ ((Znth k_2 revenue_l_2 (0 : Int)) <= (k_2 * 1000000))))) ,
  (RodCutScanBest price_l revenue_l_2 j 1 (0 : Int))

noncomputable def rod_cutting_entail_wit_3_1 : Prop :=
  (
forall (n_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (best < ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l_2 (0 : Int))))) (PreH2 : (i <= j)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) (PreH6 : (1 <= j)) (PreH7 : (j <= n_pre)) (PreH8 : (1 <= i)) (PreH9 : (i <= (j + 1))) (PreH10 : ((0 : Int) <= best)) (PreH11 : (best <= (j * 1000000))) (PreH12 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH13 : (RodCutScanBest price_l revenue_l_2 j i best)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < j)) -> (((0 : Int) <= (Znth k revenue_l_2 (0 : Int))) ∧ ((Znth k revenue_l_2 (0 : Int)) <= (k * 1000000))))) ,
  (intArray.seg ( &( "revenue" ) ) (0 : Int) j revenue_l_2)
  ** (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.undef_seg ( &( "revenue" ) ) j 1001)
|--
  EX revenue_l : (List Int),
  “ (n_pre <= 1000) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) price_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000000)) price_l) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= (j + 1)) ” &&
  “ ((0 : Int) <= ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l_2 (0 : Int)))) ” &&
  “ (((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l_2 (0 : Int))) <= (j * 1000000)) ” &&
  “ (RodCutRevenueTable price_l revenue_l j) ” &&
  “ (RodCutScanBest price_l revenue_l j (i + 1) ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l_2 (0 : Int)))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < j)) -> (((0 : Int) <= (Znth k revenue_l (0 : Int))) ∧ ((Znth k revenue_l (0 : Int)) <= (k * 1000000)))) ”
  &&  (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.seg ( &( "revenue" ) ) (0 : Int) j revenue_l)
  ** (intArray.undef_seg ( &( "revenue" ) ) j 1001)
) \/
(
forall (n_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (best < ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l_2 (0 : Int))))) (PreH2 : (i <= j)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) (PreH6 : (1 <= j)) (PreH7 : (j <= n_pre)) (PreH8 : (1 <= i)) (PreH9 : (i <= (j + 1))) (PreH10 : ((0 : Int) <= best)) (PreH11 : (best <= (j * 1000000))) (PreH12 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH13 : (RodCutScanBest price_l revenue_l_2 j i best)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < j)) -> (((0 : Int) <= (Znth k revenue_l_2 (0 : Int))) ∧ ((Znth k revenue_l_2 (0 : Int)) <= (k * 1000000))))) ,
  TT && emp 
|--
  “ (RodCutScanBest price_l revenue_l_2 j (i + 1) ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l_2 (0 : Int)))) ” &&
  “ (((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l_2 (0 : Int))) <= (j * 1000000)) ”
  &&  emp
)

noncomputable def rod_cutting_entail_wit_3_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (best < ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l_2 (0 : Int))))) (PreH2 : (i <= j)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) (PreH6 : (1 <= j)) (PreH7 : (j <= n_pre)) (PreH8 : (1 <= i)) (PreH9 : (i <= (j + 1))) (PreH10 : ((0 : Int) <= best)) (PreH11 : (best <= (j * 1000000))) (PreH12 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH13 : (RodCutScanBest price_l revenue_l_2 j i best)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < j)) -> (((0 : Int) <= (Znth k revenue_l_2 (0 : Int))) ∧ ((Znth k revenue_l_2 (0 : Int)) <= (k * 1000000))))) ,
  (RodCutScanBest price_l revenue_l_2 j (i + 1) ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l_2 (0 : Int))))

noncomputable def rod_cutting_entail_wit_3_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (best < ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l_2 (0 : Int))))) (PreH2 : (i <= j)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) (PreH6 : (1 <= j)) (PreH7 : (j <= n_pre)) (PreH8 : (1 <= i)) (PreH9 : (i <= (j + 1))) (PreH10 : ((0 : Int) <= best)) (PreH11 : (best <= (j * 1000000))) (PreH12 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH13 : (RodCutScanBest price_l revenue_l_2 j i best)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < j)) -> (((0 : Int) <= (Znth k revenue_l_2 (0 : Int))) ∧ ((Znth k revenue_l_2 (0 : Int)) <= (k * 1000000))))) ,
  (((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l_2 (0 : Int))) <= (j * 1000000))

noncomputable def rod_cutting_entail_wit_3_2 : Prop :=
  (
forall (n_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (best >= ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l_2 (0 : Int))))) (PreH2 : (i <= j)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) (PreH6 : (1 <= j)) (PreH7 : (j <= n_pre)) (PreH8 : (1 <= i)) (PreH9 : (i <= (j + 1))) (PreH10 : ((0 : Int) <= best)) (PreH11 : (best <= (j * 1000000))) (PreH12 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH13 : (RodCutScanBest price_l revenue_l_2 j i best)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < j)) -> (((0 : Int) <= (Znth k revenue_l_2 (0 : Int))) ∧ ((Znth k revenue_l_2 (0 : Int)) <= (k * 1000000))))) ,
  (intArray.seg ( &( "revenue" ) ) (0 : Int) j revenue_l_2)
  ** (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.undef_seg ( &( "revenue" ) ) j 1001)
|--
  EX revenue_l : (List Int),
  “ (n_pre <= 1000) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) price_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000000)) price_l) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= (j + 1)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= (j * 1000000)) ” &&
  “ (RodCutRevenueTable price_l revenue_l j) ” &&
  “ (RodCutScanBest price_l revenue_l j (i + 1) best) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < j)) -> (((0 : Int) <= (Znth k revenue_l (0 : Int))) ∧ ((Znth k revenue_l (0 : Int)) <= (k * 1000000)))) ”
  &&  (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.seg ( &( "revenue" ) ) (0 : Int) j revenue_l)
  ** (intArray.undef_seg ( &( "revenue" ) ) j 1001)
) \/
(
forall (n_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (best >= ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l_2 (0 : Int))))) (PreH2 : (i <= j)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) (PreH6 : (1 <= j)) (PreH7 : (j <= n_pre)) (PreH8 : (1 <= i)) (PreH9 : (i <= (j + 1))) (PreH10 : ((0 : Int) <= best)) (PreH11 : (best <= (j * 1000000))) (PreH12 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH13 : (RodCutScanBest price_l revenue_l_2 j i best)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < j)) -> (((0 : Int) <= (Znth k revenue_l_2 (0 : Int))) ∧ ((Znth k revenue_l_2 (0 : Int)) <= (k * 1000000))))) ,
  TT && emp 
|--
  “ (RodCutScanBest price_l revenue_l_2 j (i + 1) best) ”
  &&  emp
)

noncomputable def rod_cutting_entail_wit_3_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (best >= ((Znth i price_l (0 : Int)) + (Znth ((j - i) - (0 : Int)) revenue_l_2 (0 : Int))))) (PreH2 : (i <= j)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) (PreH6 : (1 <= j)) (PreH7 : (j <= n_pre)) (PreH8 : (1 <= i)) (PreH9 : (i <= (j + 1))) (PreH10 : ((0 : Int) <= best)) (PreH11 : (best <= (j * 1000000))) (PreH12 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH13 : (RodCutScanBest price_l revenue_l_2 j i best)) (PreH14 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < j)) -> (((0 : Int) <= (Znth k revenue_l_2 (0 : Int))) ∧ ((Znth k revenue_l_2 (0 : Int)) <= (k * 1000000))))) ,
  (RodCutScanBest price_l revenue_l_2 j (i + 1) best)

noncomputable def rod_cutting_entail_wit_4 : Prop :=
  (
forall (n_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (i > j)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) (PreH5 : (1 <= j)) (PreH6 : (j <= n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (j + 1))) (PreH9 : ((0 : Int) <= best)) (PreH10 : (best <= (j * 1000000))) (PreH11 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH12 : (RodCutScanBest price_l revenue_l_2 j i best)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l_2 (0 : Int))) ∧ ((Znth k_2 revenue_l_2 (0 : Int)) <= (k_2 * 1000000))))) ,
  (intArray.seg ( &( "revenue" ) ) (0 : Int) (j + 1) (revenue_l_2 ++ (best :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "revenue" ) ) (j + 1) 1001)
  ** (intArray.full price_pre (n_pre + 1) price_l)
|--
  EX revenue_l : (List Int),
  “ (n_pre <= 1000) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) price_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000000)) price_l) ” &&
  “ (1 <= (j + 1)) ” &&
  “ ((j + 1) <= (n_pre + 1)) ” &&
  “ (RodCutRevenueTable price_l revenue_l (j + 1)) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (j + 1))) -> (((0 : Int) <= (Znth k revenue_l (0 : Int))) ∧ ((Znth k revenue_l (0 : Int)) <= (k * 1000000)))) ”
  &&  (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.seg ( &( "revenue" ) ) (0 : Int) (j + 1) revenue_l)
  ** (intArray.undef_seg ( &( "revenue" ) ) (j + 1) 1001)
) \/
(
forall (n_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (i > j)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) (PreH5 : (1 <= j)) (PreH6 : (j <= n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (j + 1))) (PreH9 : ((0 : Int) <= best)) (PreH10 : (best <= (j * 1000000))) (PreH11 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH12 : (RodCutScanBest price_l revenue_l_2 j i best)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l_2 (0 : Int))) ∧ ((Znth k_2 revenue_l_2 (0 : Int)) <= (k_2 * 1000000))))) ,
  TT && emp 
|--
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (j + 1))) -> (((0 : Int) <= (Znth k (revenue_l_2 ++ (best :: (@List.nil Int))) (0 : Int))) ∧ ((Znth k (revenue_l_2 ++ (best :: (@List.nil Int))) (0 : Int)) <= (k * 1000000)))) ” &&
  “ (RodCutRevenueTable price_l (revenue_l_2 ++ (best :: (@List.nil Int))) (j + 1)) ”
  &&  emp
)

noncomputable def rod_cutting_entail_wit_4_split_goal_1 : Prop :=
  forall (n_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (i > j)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) (PreH5 : (1 <= j)) (PreH6 : (j <= n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (j + 1))) (PreH9 : ((0 : Int) <= best)) (PreH10 : (best <= (j * 1000000))) (PreH11 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH12 : (RodCutScanBest price_l revenue_l_2 j i best)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l_2 (0 : Int))) ∧ ((Znth k_2 revenue_l_2 (0 : Int)) <= (k_2 * 1000000))))) ,
  forall (k : Int) , ((((0 : Int) <= k) ∧ (k < (j + 1))) -> (((0 : Int) <= (Znth k (revenue_l_2 ++ (best :: (@List.nil Int))) (0 : Int))) ∧ ((Znth k (revenue_l_2 ++ (best :: (@List.nil Int))) (0 : Int)) <= (k * 1000000))))

noncomputable def rod_cutting_entail_wit_4_split_goal_2 : Prop :=
  forall (n_pre : Int) (price_l : (List Int)) (revenue_l_2 : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (i > j)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) (PreH5 : (1 <= j)) (PreH6 : (j <= n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (j + 1))) (PreH9 : ((0 : Int) <= best)) (PreH10 : (best <= (j * 1000000))) (PreH11 : (RodCutRevenueTable price_l revenue_l_2 j)) (PreH12 : (RodCutScanBest price_l revenue_l_2 j i best)) (PreH13 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < j)) -> (((0 : Int) <= (Znth k_2 revenue_l_2 (0 : Int))) ∧ ((Znth k_2 revenue_l_2 (0 : Int)) <= (k_2 * 1000000))))) ,
  (RodCutRevenueTable price_l (revenue_l_2 ++ (best :: (@List.nil Int))) (j + 1))

noncomputable def rod_cutting_entail_wit_5 : Prop :=
  (
forall (n_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l : (List Int)) (j : Int) (PreH1 : (j > n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) (PreH5 : (1 <= j)) (PreH6 : (j <= (n_pre + 1))) (PreH7 : (RodCutRevenueTable price_l revenue_l j)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < j)) -> (((0 : Int) <= (Znth k revenue_l (0 : Int))) ∧ ((Znth k revenue_l (0 : Int)) <= (k * 1000000))))) ,
  (intArray.seg ( &( "revenue" ) ) (0 : Int) j revenue_l)
  ** (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.undef_seg ( &( "revenue" ) ) j 1001)
|--
  “ (j = (n_pre + 1)) ” &&
  “ (RodCutOptimalRevenue price_l n_pre (Znth (n_pre - (0 : Int)) revenue_l (0 : Int))) ”
  &&  (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.undef_full ( &( "revenue" ) ) 1001)
) \/
(
forall (n_pre : Int) (price_l : (List Int)) (revenue_l : (List Int)) (j : Int) (PreH1 : (j > n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) (PreH5 : (1 <= j)) (PreH6 : (j <= (n_pre + 1))) (PreH7 : (RodCutRevenueTable price_l revenue_l j)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < j)) -> (((0 : Int) <= (Znth k revenue_l (0 : Int))) ∧ ((Znth k revenue_l (0 : Int)) <= (k * 1000000))))) ,
  (intArray.seg ( &( "revenue" ) ) (0 : Int) j revenue_l)
  ** (intArray.undef_seg ( &( "revenue" ) ) j 1001)
|--
  “ (RodCutOptimalRevenue price_l n_pre (Znth (n_pre - (0 : Int)) revenue_l (0 : Int))) ”
  &&  (intArray.undef_full ( &( "revenue" ) ) 1001)
)

noncomputable def rod_cutting_entail_wit_5_split_goal_1 : Prop :=
  forall (n_pre : Int) (price_l : (List Int)) (revenue_l : (List Int)) (j : Int) (PreH1 : (j > n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) (PreH5 : (1 <= j)) (PreH6 : (j <= (n_pre + 1))) (PreH7 : (RodCutRevenueTable price_l revenue_l j)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < j)) -> (((0 : Int) <= (Znth k revenue_l (0 : Int))) ∧ ((Znth k revenue_l (0 : Int)) <= (k * 1000000))))) ,
  (intArray.seg ( &( "revenue" ) ) (0 : Int) j revenue_l)
  ** (intArray.undef_seg ( &( "revenue" ) ) j 1001)
|--
  “ (RodCutOptimalRevenue price_l n_pre (Znth (n_pre - (0 : Int)) revenue_l (0 : Int))) ”

noncomputable def rod_cutting_entail_wit_5_split_goal_spatial : Prop :=
  forall (n_pre : Int) (price_l : (List Int)) (revenue_l : (List Int)) (j : Int) (PreH1 : (j > n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) (PreH5 : (1 <= j)) (PreH6 : (j <= (n_pre + 1))) (PreH7 : (RodCutRevenueTable price_l revenue_l j)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < j)) -> (((0 : Int) <= (Znth k revenue_l (0 : Int))) ∧ ((Znth k revenue_l (0 : Int)) <= (k * 1000000))))) ,
  (intArray.seg ( &( "revenue" ) ) (0 : Int) j revenue_l)
  ** (intArray.undef_seg ( &( "revenue" ) ) j 1001)
|--
  (intArray.undef_full ( &( "revenue" ) ) 1001)

noncomputable def rod_cutting_return_wit_1 : Prop :=
  forall (n_pre : Int) (price_pre : Int) (price_l : (List Int)) (j : Int) (result : Int) (PreH1 : (j = (n_pre + 1))) (PreH2 : (RodCutOptimalRevenue price_l n_pre result)) ,
  (intArray.full price_pre (n_pre + 1) price_l)
|--
  “ (RodCutOptimalRevenue price_l n_pre result) ”
  &&  (intArray.full price_pre (n_pre + 1) price_l)

noncomputable def rod_cutting_partial_solve_wit_1 : Prop :=
  forall (n_pre : Int) (price_pre : Int) (price_l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (price_l)) = (n_pre + 1))) (PreH4 : ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int))) (PreH5 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH6 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) ,
  (intArray.undef_full ( &( "revenue" ) ) 1001)
  ** (intArray.full price_pre (n_pre + 1) price_l)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (price_l)) = (n_pre + 1)) ” &&
  “ ((Znth (0 : Int) price_l (0 : Int)) = (0 : Int)) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) price_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000000)) price_l) ”
  &&  (((( &( "revenue" ) ) + ((0 : Int) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg ( &( "revenue" ) ) 1 1001)
  ** (intArray.full price_pre (n_pre + 1) price_l)

noncomputable def rod_cutting_partial_solve_wit_2 : Prop :=
  forall (n_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (i <= j)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) (PreH5 : (1 <= j)) (PreH6 : (j <= n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (j + 1))) (PreH9 : ((0 : Int) <= best)) (PreH10 : (best <= (j * 1000000))) (PreH11 : (RodCutRevenueTable price_l revenue_l j)) (PreH12 : (RodCutScanBest price_l revenue_l j i best)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < j)) -> (((0 : Int) <= (Znth k revenue_l (0 : Int))) ∧ ((Znth k revenue_l (0 : Int)) <= (k * 1000000))))) ,
  (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.seg ( &( "revenue" ) ) (0 : Int) j revenue_l)
  ** (intArray.undef_seg ( &( "revenue" ) ) j 1001)
|--
  “ (i <= j) ” &&
  “ (n_pre <= 1000) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) price_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000000)) price_l) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= (j + 1)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= (j * 1000000)) ” &&
  “ (RodCutRevenueTable price_l revenue_l j) ” &&
  “ (RodCutScanBest price_l revenue_l j i best) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < j)) -> (((0 : Int) <= (Znth k revenue_l (0 : Int))) ∧ ((Znth k revenue_l (0 : Int)) <= (k * 1000000)))) ”
  &&  (((price_pre + (i * sizeof(INT)))) # Int |-> ((Znth i price_l (0 : Int))))
  ** (intArray.missing_i price_pre i (0 : Int) (n_pre + 1) price_l)
  ** (intArray.seg ( &( "revenue" ) ) (0 : Int) j revenue_l)
  ** (intArray.undef_seg ( &( "revenue" ) ) j 1001)

noncomputable def rod_cutting_partial_solve_wit_3 : Prop :=
  forall (n_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (i <= j)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) (PreH5 : (1 <= j)) (PreH6 : (j <= n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (j + 1))) (PreH9 : ((0 : Int) <= best)) (PreH10 : (best <= (j * 1000000))) (PreH11 : (RodCutRevenueTable price_l revenue_l j)) (PreH12 : (RodCutScanBest price_l revenue_l j i best)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < j)) -> (((0 : Int) <= (Znth k revenue_l (0 : Int))) ∧ ((Znth k revenue_l (0 : Int)) <= (k * 1000000))))) ,
  (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.seg ( &( "revenue" ) ) (0 : Int) j revenue_l)
  ** (intArray.undef_seg ( &( "revenue" ) ) j 1001)
|--
  “ (i <= j) ” &&
  “ (n_pre <= 1000) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) price_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000000)) price_l) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= (j + 1)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= (j * 1000000)) ” &&
  “ (RodCutRevenueTable price_l revenue_l j) ” &&
  “ (RodCutScanBest price_l revenue_l j i best) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < j)) -> (((0 : Int) <= (Znth k revenue_l (0 : Int))) ∧ ((Znth k revenue_l (0 : Int)) <= (k * 1000000)))) ”
  &&  (((( &( "revenue" ) ) + ((j - i) * sizeof(INT)))) # Int |-> ((Znth ((j - i) - (0 : Int)) revenue_l (0 : Int))))
  ** (intArray.missing_i ( &( "revenue" ) ) (j - i) (0 : Int) j revenue_l)
  ** (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.undef_seg ( &( "revenue" ) ) j 1001)

noncomputable def rod_cutting_partial_solve_wit_4 : Prop :=
  forall (n_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l : (List Int)) (best : Int) (i : Int) (j : Int) (PreH1 : (i > j)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) (PreH5 : (1 <= j)) (PreH6 : (j <= n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (j + 1))) (PreH9 : ((0 : Int) <= best)) (PreH10 : (best <= (j * 1000000))) (PreH11 : (RodCutRevenueTable price_l revenue_l j)) (PreH12 : (RodCutScanBest price_l revenue_l j i best)) (PreH13 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < j)) -> (((0 : Int) <= (Znth k revenue_l (0 : Int))) ∧ ((Znth k revenue_l (0 : Int)) <= (k * 1000000))))) ,
  (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.seg ( &( "revenue" ) ) (0 : Int) j revenue_l)
  ** (intArray.undef_seg ( &( "revenue" ) ) j 1001)
|--
  “ (i > j) ” &&
  “ (n_pre <= 1000) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) price_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000000)) price_l) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= (j + 1)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= (j * 1000000)) ” &&
  “ (RodCutRevenueTable price_l revenue_l j) ” &&
  “ (RodCutScanBest price_l revenue_l j i best) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < j)) -> (((0 : Int) <= (Znth k revenue_l (0 : Int))) ∧ ((Znth k revenue_l (0 : Int)) <= (k * 1000000)))) ”
  &&  (((( &( "revenue" ) ) + (j * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg ( &( "revenue" ) ) (j + 1) 1001)
  ** (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.seg ( &( "revenue" ) ) (0 : Int) j revenue_l)

noncomputable def rod_cutting_partial_solve_wit_5 : Prop :=
  forall (n_pre : Int) (price_pre : Int) (price_l : (List Int)) (revenue_l : (List Int)) (j : Int) (PreH1 : (j > n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall ((LE.le (α := Int)) ((0 : Int))) price_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000000)) price_l)) (PreH5 : (1 <= j)) (PreH6 : (j <= (n_pre + 1))) (PreH7 : (RodCutRevenueTable price_l revenue_l j)) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < j)) -> (((0 : Int) <= (Znth k revenue_l (0 : Int))) ∧ ((Znth k revenue_l (0 : Int)) <= (k * 1000000))))) ,
  (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.seg ( &( "revenue" ) ) (0 : Int) j revenue_l)
  ** (intArray.undef_seg ( &( "revenue" ) ) j 1001)
|--
  “ (j > n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) price_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000000)) price_l) ” &&
  “ (1 <= j) ” &&
  “ (j <= (n_pre + 1)) ” &&
  “ (RodCutRevenueTable price_l revenue_l j) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < j)) -> (((0 : Int) <= (Znth k revenue_l (0 : Int))) ∧ ((Znth k revenue_l (0 : Int)) <= (k * 1000000)))) ”
  &&  (((( &( "revenue" ) ) + (n_pre * sizeof(INT)))) # Int |-> ((Znth (n_pre - (0 : Int)) revenue_l (0 : Int))))
  ** (intArray.missing_i ( &( "revenue" ) ) n_pre (0 : Int) j revenue_l)
  ** (intArray.full price_pre (n_pre + 1) price_l)
  ** (intArray.undef_seg ( &( "revenue" ) ) j 1001)


structure VC_Correct : Type where
  proof_of_rod_cutting_safety_wit_1 : rod_cutting_safety_wit_1
  proof_of_rod_cutting_safety_wit_2 : rod_cutting_safety_wit_2
  proof_of_rod_cutting_safety_wit_3 : rod_cutting_safety_wit_3
  proof_of_rod_cutting_safety_wit_4 : rod_cutting_safety_wit_4
  proof_of_rod_cutting_safety_wit_5 : rod_cutting_safety_wit_5
  proof_of_rod_cutting_safety_wit_7 : rod_cutting_safety_wit_7
  proof_of_rod_cutting_safety_wit_8 : rod_cutting_safety_wit_8
  proof_of_rod_cutting_safety_wit_9 : rod_cutting_safety_wit_9
  proof_of_rod_cutting_safety_wit_10 : rod_cutting_safety_wit_10
  proof_of_rod_cutting_return_wit_1 : rod_cutting_return_wit_1
  proof_of_rod_cutting_partial_solve_wit_1 : rod_cutting_partial_solve_wit_1
  proof_of_rod_cutting_partial_solve_wit_2 : rod_cutting_partial_solve_wit_2
  proof_of_rod_cutting_partial_solve_wit_3 : rod_cutting_partial_solve_wit_3
  proof_of_rod_cutting_partial_solve_wit_4 : rod_cutting_partial_solve_wit_4
  proof_of_rod_cutting_partial_solve_wit_5 : rod_cutting_partial_solve_wit_5
  proof_of_rod_cutting_safety_wit_6 : rod_cutting_safety_wit_6
  proof_of_rod_cutting_entail_wit_1 : rod_cutting_entail_wit_1
  proof_of_rod_cutting_entail_wit_2 : rod_cutting_entail_wit_2
  proof_of_rod_cutting_entail_wit_3_1 : rod_cutting_entail_wit_3_1
  proof_of_rod_cutting_entail_wit_3_2 : rod_cutting_entail_wit_3_2
  proof_of_rod_cutting_entail_wit_4 : rod_cutting_entail_wit_4
  proof_of_rod_cutting_entail_wit_5 : rod_cutting_entail_wit_5

end SimpleC.EE.LLM_bench.Algorithms.rod_cutting.rod_cutting_goal
