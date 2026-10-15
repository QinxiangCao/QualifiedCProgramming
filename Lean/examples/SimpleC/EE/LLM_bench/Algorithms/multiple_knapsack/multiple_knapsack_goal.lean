import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.multiple_knapsack.multiple_knapsack_lib
open SimpleC.EE.LLM_bench.Algorithms.multiple_knapsack.multiple_knapsack_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.multiple_knapsack.multiple_knapsack_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance multiple_knapsack_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def multipleKnapsack_safety_wit_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH9 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH11 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH13 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  ((( &( "j" ) )) # Int |->_)
  ** (intArray.undef_full ( &( "q_val" ) ) 1001)
  ** (intArray.undef_full ( &( "q_idx" ) ) 1001)
  ** (intArray.undef_full ( &( "old" ) ) 1001)
  ** (intArray.undef_full ( &( "dp" ) ) 1001)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def multipleKnapsack_safety_wit_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (qval0 : (List Int)) (qidx0 : (List Int)) (old0 : (List Int)) (j : Int) (dp_l : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = j)) (PreH10 : ((Zlength (old0)) = j)) (PreH11 : ((Zlength (qidx0)) = j)) (PreH12 : ((Zlength (qval0)) = j)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= (capacity_pre + 1))) (PreH15 : (Forall (Eq ((0 : Int))) dp_l)) (PreH16 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH17 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) j dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) j 1001)
  ** (intArray.seg ( &( "old" ) ) (0 : Int) j old0)
  ** (intArray.undef_seg ( &( "old" ) ) j 1001)
  ** (intArray.seg ( &( "q_idx" ) ) (0 : Int) j qidx0)
  ** (intArray.undef_seg ( &( "q_idx" ) ) j 1001)
  ** (intArray.seg ( &( "q_val" ) ) (0 : Int) j qval0)
  ** (intArray.undef_seg ( &( "q_val" ) ) j 1001)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def multipleKnapsack_safety_wit_3 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (qval0 : (List Int)) (qidx0 : (List Int)) (old0 : (List Int)) (j : Int) (dp_l : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = j)) (PreH10 : ((Zlength (old0)) = j)) (PreH11 : ((Zlength (qidx0)) = j)) (PreH12 : ((Zlength (qval0)) = j)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= (capacity_pre + 1))) (PreH15 : (Forall (Eq ((0 : Int))) dp_l)) (PreH16 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH17 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.seg ( &( "dp" ) ) (0 : Int) (j + 1) (dp_l ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "dp" ) ) (j + 1) 1001)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.seg ( &( "old" ) ) (0 : Int) j old0)
  ** (intArray.undef_seg ( &( "old" ) ) j 1001)
  ** (intArray.seg ( &( "q_idx" ) ) (0 : Int) j qidx0)
  ** (intArray.undef_seg ( &( "q_idx" ) ) j 1001)
  ** (intArray.seg ( &( "q_val" ) ) (0 : Int) j qval0)
  ** (intArray.undef_seg ( &( "q_val" ) ) j 1001)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def multipleKnapsack_safety_wit_4 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (qval0 : (List Int)) (qidx0 : (List Int)) (old0 : (List Int)) (j : Int) (dp_l : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = j)) (PreH10 : ((Zlength (old0)) = j)) (PreH11 : ((Zlength (qidx0)) = j)) (PreH12 : ((Zlength (qval0)) = j)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= (capacity_pre + 1))) (PreH15 : (Forall (Eq ((0 : Int))) dp_l)) (PreH16 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH17 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.seg ( &( "old" ) ) (0 : Int) (j + 1) (old0 ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "old" ) ) (j + 1) 1001)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) (j + 1) (dp_l ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "dp" ) ) (j + 1) 1001)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.seg ( &( "q_idx" ) ) (0 : Int) j qidx0)
  ** (intArray.undef_seg ( &( "q_idx" ) ) j 1001)
  ** (intArray.seg ( &( "q_val" ) ) (0 : Int) j qval0)
  ** (intArray.undef_seg ( &( "q_val" ) ) j 1001)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def multipleKnapsack_safety_wit_5 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (qval0 : (List Int)) (qidx0 : (List Int)) (old0 : (List Int)) (j : Int) (dp_l : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = j)) (PreH10 : ((Zlength (old0)) = j)) (PreH11 : ((Zlength (qidx0)) = j)) (PreH12 : ((Zlength (qval0)) = j)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= (capacity_pre + 1))) (PreH15 : (Forall (Eq ((0 : Int))) dp_l)) (PreH16 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH17 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.seg ( &( "q_idx" ) ) (0 : Int) (j + 1) (qidx0 ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "q_idx" ) ) (j + 1) 1001)
  ** (intArray.seg ( &( "old" ) ) (0 : Int) (j + 1) (old0 ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "old" ) ) (j + 1) 1001)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) (j + 1) (dp_l ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "dp" ) ) (j + 1) 1001)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.seg ( &( "q_val" ) ) (0 : Int) j qval0)
  ** (intArray.undef_seg ( &( "q_val" ) ) j 1001)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def multipleKnapsack_safety_wit_6 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (qval0 : (List Int)) (qidx0 : (List Int)) (old0 : (List Int)) (j : Int) (dp_l : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = j)) (PreH10 : ((Zlength (old0)) = j)) (PreH11 : ((Zlength (qidx0)) = j)) (PreH12 : ((Zlength (qval0)) = j)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= (capacity_pre + 1))) (PreH15 : (Forall (Eq ((0 : Int))) dp_l)) (PreH16 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH17 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.seg ( &( "q_val" ) ) (0 : Int) (j + 1) (qval0 ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "q_val" ) ) (j + 1) 1001)
  ** (intArray.seg ( &( "q_idx" ) ) (0 : Int) (j + 1) (qidx0 ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "q_idx" ) ) (j + 1) 1001)
  ** (intArray.seg ( &( "old" ) ) (0 : Int) (j + 1) (old0 ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "old" ) ) (j + 1) 1001)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) (j + 1) (dp_l ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "dp" ) ) (j + 1) 1001)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def multipleKnapsack_safety_wit_7 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (qval0 : (List Int)) (qidx0 : (List Int)) (old0 : (List Int)) (j : Int) (dp_l : (List Int)) (PreH1 : (j > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = j)) (PreH10 : ((Zlength (old0)) = j)) (PreH11 : ((Zlength (qidx0)) = j)) (PreH12 : ((Zlength (qval0)) = j)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= (capacity_pre + 1))) (PreH15 : (Forall (Eq ((0 : Int))) dp_l)) (PreH16 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH17 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) j dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) j 1001)
  ** (intArray.seg ( &( "old" ) ) (0 : Int) j old0)
  ** (intArray.undef_seg ( &( "old" ) ) j 1001)
  ** (intArray.seg ( &( "q_idx" ) ) (0 : Int) j qidx0)
  ** (intArray.undef_seg ( &( "q_idx" ) ) j 1001)
  ** (intArray.seg ( &( "q_val" ) ) (0 : Int) j qval0)
  ** (intArray.undef_seg ( &( "q_val" ) ) j 1001)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def multipleKnapsack_safety_wit_8 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l)) (PreH16 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH17 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def multipleKnapsack_safety_wit_9 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l)) (PreH18 : (MKCopyPrefixSemantics dp_l old_l j)) (PreH19 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH20 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH22 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH23 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH24 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "old" ) ) (capacity_pre + 1) (replace_Znth (j) ((Znth j dp_l (0 : Int))) (old_l)))
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def multipleKnapsack_safety_wit_10 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (j > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l)) (PreH18 : (MKCopyPrefixSemantics dp_l old_l j)) (PreH19 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH20 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH22 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH23 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH24 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  ((( &( "r" ) )) # Int |->_)
  ** (intArray.full counts_pre n_pre counts_l)
  ** ((( &( "cnt" ) )) # Int |-> ((Znth i counts_l (0 : Int))))
  ** (intArray.full values_pre n_pre values_l)
  ** ((( &( "v" ) )) # Int |-> ((Znth i values_l (0 : Int))))
  ** (intArray.full weights_pre n_pre weights_l)
  ** ((( &( "w" ) )) # Int |-> ((Znth i weights_l (0 : Int))))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def multipleKnapsack_safety_wit_11 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (r : Int) (cnt : Int) (v : Int) (w : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (r > capacity_pre)) (PreH2 : (r < w)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : (w = (Znth i weights_l (0 : Int)))) (PreH17 : (v = (Znth i values_l (0 : Int)))) (PreH18 : (cnt = (Znth i counts_l (0 : Int)))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1))) (PreH21 : ((0 : Int) <= v)) (PreH22 : (v <= 1000)) (PreH23 : ((0 : Int) <= cnt)) (PreH24 : (cnt <= capacity_pre)) (PreH25 : ((0 : Int) <= r)) (PreH26 : (r <= w)) (PreH27 : (r <= (capacity_pre + 1))) (PreH28 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH30 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH31 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH32 : (MKItemResidueProgressSemantics old_l dp_l r w v cnt capacity_pre)) (PreH33 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH34 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ False ”

noncomputable def multipleKnapsack_safety_wit_12 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (r : Int) (cnt : Int) (v : Int) (w : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (r <= capacity_pre)) (PreH2 : (r < w)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : (w = (Znth i weights_l (0 : Int)))) (PreH17 : (v = (Znth i values_l (0 : Int)))) (PreH18 : (cnt = (Znth i counts_l (0 : Int)))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1))) (PreH21 : ((0 : Int) <= v)) (PreH22 : (v <= 1000)) (PreH23 : ((0 : Int) <= cnt)) (PreH24 : (cnt <= capacity_pre)) (PreH25 : ((0 : Int) <= r)) (PreH26 : (r <= w)) (PreH27 : (r <= (capacity_pre + 1))) (PreH28 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH30 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH31 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH32 : (MKItemResidueProgressSemantics old_l dp_l r w v cnt capacity_pre)) (PreH33 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH34 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  ((( &( "head" ) )) # Int |->_)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def multipleKnapsack_safety_wit_13 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (r : Int) (cnt : Int) (v : Int) (w : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (r <= capacity_pre)) (PreH2 : (r < w)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : (w = (Znth i weights_l (0 : Int)))) (PreH17 : (v = (Znth i values_l (0 : Int)))) (PreH18 : (cnt = (Znth i counts_l (0 : Int)))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1))) (PreH21 : ((0 : Int) <= v)) (PreH22 : (v <= 1000)) (PreH23 : ((0 : Int) <= cnt)) (PreH24 : (cnt <= capacity_pre)) (PreH25 : ((0 : Int) <= r)) (PreH26 : (r <= w)) (PreH27 : (r <= (capacity_pre + 1))) (PreH28 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH30 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH31 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH32 : (MKItemResidueProgressSemantics old_l dp_l r w v cnt capacity_pre)) (PreH33 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH34 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  ((( &( "tail" ) )) # Int |->_)
  ** ((( &( "head" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def multipleKnapsack_safety_wit_14 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (r : Int) (cnt : Int) (v : Int) (w : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (r <= capacity_pre)) (PreH2 : (r < w)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : (w = (Znth i weights_l (0 : Int)))) (PreH17 : (v = (Znth i values_l (0 : Int)))) (PreH18 : (cnt = (Znth i counts_l (0 : Int)))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1))) (PreH21 : ((0 : Int) <= v)) (PreH22 : (v <= 1000)) (PreH23 : ((0 : Int) <= cnt)) (PreH24 : (cnt <= capacity_pre)) (PreH25 : ((0 : Int) <= r)) (PreH26 : (r <= w)) (PreH27 : (r <= (capacity_pre + 1))) (PreH28 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH30 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH31 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH32 : (MKItemResidueProgressSemantics old_l dp_l r w v cnt capacity_pre)) (PreH33 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH34 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  ((( &( "k" ) )) # Int |->_)
  ** ((( &( "tail" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "head" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def multipleKnapsack_safety_wit_15 : Prop :=
  (
forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (pos <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH39 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH41 : (MKQueueResultSemantics old_l qidx_l qval_l head tail r w v cnt k capacity_pre)) (PreH42 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l)))) (PreH43 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l)))) (PreH44 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH45 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH46 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH48 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH49 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** ((( &( "current" ) )) # Int |->_)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ (((Znth pos old_l (0 : Int)) - (k * v)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth pos old_l (0 : Int)) - (k * v))) ”
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (pos <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH39 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH41 : (MKQueueResultSemantics old_l qidx_l qval_l head tail r w v cnt k capacity_pre)) (PreH42 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l)))) (PreH43 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l)))) (PreH44 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH45 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH46 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH48 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH49 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** ((( &( "current" ) )) # Int |->_)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ (((Znth pos old_l (0 : Int)) - (k * v)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth pos old_l (0 : Int)) - (k * v))) ”
)

noncomputable def multipleKnapsack_safety_wit_15_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (pos <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH39 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH41 : (MKQueueResultSemantics old_l qidx_l qval_l head tail r w v cnt k capacity_pre)) (PreH42 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l)))) (PreH43 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l)))) (PreH44 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH45 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH46 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH48 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH49 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** ((( &( "current" ) )) # Int |->_)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ (((Znth pos old_l (0 : Int)) - (k * v)) <= INT_MAX) ”

noncomputable def multipleKnapsack_safety_wit_15_split_goal_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (pos <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH39 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH41 : (MKQueueResultSemantics old_l qidx_l qval_l head tail r w v cnt k capacity_pre)) (PreH42 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l)))) (PreH43 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l)))) (PreH44 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH45 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH46 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH48 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH49 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** ((( &( "current" ) )) # Int |->_)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ ((INT_MIN) <= ((Znth pos old_l (0 : Int)) - (k * v))) ”

noncomputable def multipleKnapsack_safety_wit_16 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (pos <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH39 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH41 : (MKQueueResultSemantics old_l qidx_l qval_l head tail r w v cnt k capacity_pre)) (PreH42 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l)))) (PreH43 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l)))) (PreH44 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH45 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH46 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH48 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH49 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** ((( &( "current" ) )) # Int |->_)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ ((k * v) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k * v)) ”

noncomputable def multipleKnapsack_safety_wit_17 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (head < tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH42 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH44 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH46 : (MKQueueDropSemantics old_l qidx_l qval_l head tail r w v cnt k)) (PreH47 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l)))) (PreH48 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l)))) (PreH49 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH50 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH52 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH54 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ ((k - cnt) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k - cnt)) ”

noncomputable def multipleKnapsack_safety_wit_18 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : ((Znth head qidx_l (0 : Int)) < (k - cnt))) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH45 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH47 : (MKQueueDropSemantics old_l qidx_l qval_l head tail r w v cnt k)) (PreH48 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ ((head + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (head + 1)) ”

noncomputable def multipleKnapsack_safety_wit_19 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (head < tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH42 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH44 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH46 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH47 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l)))) (PreH48 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l)))) (PreH49 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH50 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH52 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH54 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ ((tail - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (tail - 1)) ”

noncomputable def multipleKnapsack_safety_wit_20 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (head < tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH42 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH44 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH46 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH47 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l)))) (PreH48 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l)))) (PreH49 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH50 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH52 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH54 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def multipleKnapsack_safety_wit_21 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l (0 : Int)) <= current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH45 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH47 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH48 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ ((tail - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (tail - 1)) ”

noncomputable def multipleKnapsack_safety_wit_22 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH42 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH44 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH46 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH47 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l)))) (PreH48 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l)))) (PreH49 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH50 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH52 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH54 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) (replace_Znth (tail) (current) (qval_l)))
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ ((tail + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (tail + 1)) ”

noncomputable def multipleKnapsack_safety_wit_23 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l (0 : Int)) > current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH45 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH47 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH48 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) (replace_Znth (tail) (current) (qval_l)))
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> (tail))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ ((tail + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (tail + 1)) ”

noncomputable def multipleKnapsack_safety_wit_24 : Prop :=
  (
forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH42 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH44 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH46 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH47 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l)))) (PreH48 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l)))) (PreH49 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH50 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH52 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH54 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) (replace_Znth (tail) (current) (qval_l)))
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> ((tail + 1)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ (((Znth head (replace_Znth (tail) (current) (qval_l)) (0 : Int)) + (k * v)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth head (replace_Znth (tail) (current) (qval_l)) (0 : Int)) + (k * v))) ”
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH42 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH44 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH46 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH47 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l)))) (PreH48 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l)))) (PreH49 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH50 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH52 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH54 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) (replace_Znth (tail) (current) (qval_l)))
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> ((tail + 1)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ (((Znth head (replace_Znth (tail) (current) (qval_l)) (0 : Int)) + (k * v)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth head (replace_Znth (tail) (current) (qval_l)) (0 : Int)) + (k * v))) ”
)

noncomputable def multipleKnapsack_safety_wit_24_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH42 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH44 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH46 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH47 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l)))) (PreH48 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l)))) (PreH49 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH50 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH52 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH54 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) (replace_Znth (tail) (current) (qval_l)))
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> ((tail + 1)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ (((Znth head (replace_Znth (tail) (current) (qval_l)) (0 : Int)) + (k * v)) <= INT_MAX) ”

noncomputable def multipleKnapsack_safety_wit_24_split_goal_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH42 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH44 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH46 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH47 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l)))) (PreH48 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l)))) (PreH49 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH50 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH52 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH54 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) (replace_Znth (tail) (current) (qval_l)))
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> ((tail + 1)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ ((INT_MIN) <= ((Znth head (replace_Znth (tail) (current) (qval_l)) (0 : Int)) + (k * v))) ”

noncomputable def multipleKnapsack_safety_wit_25 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH42 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH44 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH46 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH47 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l)))) (PreH48 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l)))) (PreH49 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH50 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH52 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH54 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) (replace_Znth (tail) (current) (qval_l)))
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> ((tail + 1)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ ((k * v) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k * v)) ”

noncomputable def multipleKnapsack_safety_wit_26 : Prop :=
  (
forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l (0 : Int)) > current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH45 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH47 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH48 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) (replace_Znth (tail) (current) (qval_l)))
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> ((tail + 1)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ (((Znth head (replace_Znth (tail) (current) (qval_l)) (0 : Int)) + (k * v)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth head (replace_Znth (tail) (current) (qval_l)) (0 : Int)) + (k * v))) ”
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l (0 : Int)) > current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH45 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH47 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH48 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) (replace_Znth (tail) (current) (qval_l)))
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> ((tail + 1)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ (((Znth head (replace_Znth (tail) (current) (qval_l)) (0 : Int)) + (k * v)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth head (replace_Znth (tail) (current) (qval_l)) (0 : Int)) + (k * v))) ”
)

noncomputable def multipleKnapsack_safety_wit_26_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l (0 : Int)) > current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH45 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH47 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH48 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) (replace_Znth (tail) (current) (qval_l)))
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> ((tail + 1)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ (((Znth head (replace_Znth (tail) (current) (qval_l)) (0 : Int)) + (k * v)) <= INT_MAX) ”

noncomputable def multipleKnapsack_safety_wit_26_split_goal_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l (0 : Int)) > current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH45 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH47 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH48 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) (replace_Znth (tail) (current) (qval_l)))
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> ((tail + 1)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ ((INT_MIN) <= ((Znth head (replace_Znth (tail) (current) (qval_l)) (0 : Int)) + (k * v))) ”

noncomputable def multipleKnapsack_safety_wit_27 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l (0 : Int)) > current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH45 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH47 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH48 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) (replace_Znth (tail) (current) (qval_l)))
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> ((tail + 1)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ ((k * v) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k * v)) ”

noncomputable def multipleKnapsack_safety_wit_28 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH42 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH44 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH46 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH47 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l)))) (PreH48 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l)))) (PreH49 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH50 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH52 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH54 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "dp" ) ) (capacity_pre + 1) (replace_Znth (pos) (((Znth head (replace_Znth (tail) (current) (qval_l)) (0 : Int)) + (k * v))) (dp_l)))
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) (replace_Znth (tail) (current) (qval_l)))
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> ((tail + 1)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def multipleKnapsack_safety_wit_29 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l (0 : Int)) > current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH45 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH47 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH48 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "dp" ) ) (capacity_pre + 1) (replace_Znth (pos) (((Znth head (replace_Znth (tail) (current) (qval_l)) (0 : Int)) + (k * v))) (dp_l)))
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) (replace_Znth (tail) (current) (qval_l)))
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** ((( &( "current" ) )) # Int |-> (current))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> ((tail + 1)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def multipleKnapsack_safety_wit_30 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH42 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH44 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH46 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH47 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l)))) (PreH48 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l)))) (PreH49 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH50 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH52 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH54 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "dp" ) ) (capacity_pre + 1) (replace_Znth (pos) (((Znth head (replace_Znth (tail) (current) (qval_l)) (0 : Int)) + (k * v))) (dp_l)))
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) (replace_Znth (tail) (current) (qval_l)))
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> ((k + 1)))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> ((tail + 1)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ ((pos + w) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (pos + w)) ”

noncomputable def multipleKnapsack_safety_wit_31 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l (0 : Int)) > current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH45 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH47 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH48 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "dp" ) ) (capacity_pre + 1) (replace_Znth (pos) (((Znth head (replace_Znth (tail) (current) (qval_l)) (0 : Int)) + (k * v))) (dp_l)))
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) (replace_Znth (tail) (current) (qval_l)))
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "k" ) )) # Int |-> ((k + 1)))
  ** ((( &( "head" ) )) # Int |-> (head))
  ** ((( &( "tail" ) )) # Int |-> ((tail + 1)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ ((pos + w) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (pos + w)) ”

noncomputable def multipleKnapsack_safety_wit_32 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (pos > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH39 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH41 : (MKQueueResultSemantics old_l qidx_l qval_l head tail r w v cnt k capacity_pre)) (PreH42 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l)))) (PreH43 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l)))) (PreH44 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH45 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH46 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH48 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH49 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "r" ) )) # Int |-> (r))
  ** ((( &( "w" ) )) # Int |-> (w))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ ((r + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (r + 1)) ”

noncomputable def multipleKnapsack_safety_wit_33 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (r : Int) (cnt : Int) (v : Int) (w : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (r >= w)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : (w = (Znth i weights_l (0 : Int)))) (PreH16 : (v = (Znth i values_l (0 : Int)))) (PreH17 : (cnt = (Znth i counts_l (0 : Int)))) (PreH18 : (1 <= w)) (PreH19 : (w <= (capacity_pre + 1))) (PreH20 : ((0 : Int) <= v)) (PreH21 : (v <= 1000)) (PreH22 : ((0 : Int) <= cnt)) (PreH23 : (cnt <= capacity_pre)) (PreH24 : ((0 : Int) <= r)) (PreH25 : (r <= w)) (PreH26 : (r <= (capacity_pre + 1))) (PreH27 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH28 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH29 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH30 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH31 : (MKItemResidueProgressSemantics old_l dp_l r w v cnt capacity_pre)) (PreH32 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH33 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH34 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH35 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH36 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH37 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "counts" ) )) # Ptr |-> (counts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "capacity" ) )) # Int |-> (capacity_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def multipleKnapsack_entail_wit_1 : Prop :=
  (
forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH9 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH11 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH13 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.undef_full ( &( "q_val" ) ) 1001)
  ** (intArray.undef_full ( &( "q_idx" ) ) 1001)
  ** (intArray.undef_full ( &( "old" ) ) 1001)
  ** (intArray.undef_full ( &( "dp" ) ) 1001)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
|--
  EX qval0 : (List Int), EX qidx0 : (List Int), EX old0 : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (0 : Int)) ” &&
  “ ((Zlength (old0)) = (0 : Int)) ” &&
  “ ((Zlength (qidx0)) = (0 : Int)) ” &&
  “ ((Zlength (qval0)) = (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (capacity_pre + 1)) ” &&
  “ (Forall (Eq ((0 : Int))) dp_l) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) (0 : Int) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (0 : Int) 1001)
  ** (intArray.seg ( &( "old" ) ) (0 : Int) (0 : Int) old0)
  ** (intArray.undef_seg ( &( "old" ) ) (0 : Int) 1001)
  ** (intArray.seg ( &( "q_idx" ) ) (0 : Int) (0 : Int) qidx0)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (0 : Int) 1001)
  ** (intArray.seg ( &( "q_val" ) ) (0 : Int) (0 : Int) qval0)
  ** (intArray.undef_seg ( &( "q_val" ) ) (0 : Int) 1001)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH9 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH11 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH13 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  TT && emp 
|--
  “ (Forall (Eq ((0 : Int))) (@List.nil Int)) ” &&
  “ ((Zlength ((@List.nil Int))) = (0 : Int)) ” &&
  “ ((Zlength ((@List.nil Int))) = (0 : Int)) ” &&
  “ ((Zlength ((@List.nil Int))) = (0 : Int)) ” &&
  “ ((Zlength ((@List.nil Int))) = (0 : Int)) ”
  &&  emp
)

noncomputable def multipleKnapsack_entail_wit_1_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH9 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH11 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH13 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (Forall (Eq ((0 : Int))) (@List.nil Int))

noncomputable def multipleKnapsack_entail_wit_1_split_goal_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH9 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH11 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH13 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  ((Zlength ((@List.nil Int))) = (0 : Int))

noncomputable def multipleKnapsack_entail_wit_1_split_goal_3 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH9 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH11 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH13 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  ((Zlength ((@List.nil Int))) = (0 : Int))

noncomputable def multipleKnapsack_entail_wit_1_split_goal_4 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH9 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH11 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH13 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  ((Zlength ((@List.nil Int))) = (0 : Int))

noncomputable def multipleKnapsack_entail_wit_1_split_goal_5 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((0 : Int) <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH9 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH11 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH13 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  ((Zlength ((@List.nil Int))) = (0 : Int))

noncomputable def multipleKnapsack_entail_wit_2 : Prop :=
  (
forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (qval0_2 : (List Int)) (qidx0_2 : (List Int)) (old0_2 : (List Int)) (j : Int) (dp_l_2 : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = j)) (PreH10 : ((Zlength (old0_2)) = j)) (PreH11 : ((Zlength (qidx0_2)) = j)) (PreH12 : ((Zlength (qval0_2)) = j)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= (capacity_pre + 1))) (PreH15 : (Forall (Eq ((0 : Int))) dp_l_2)) (PreH16 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH17 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.seg ( &( "q_val" ) ) (0 : Int) (j + 1) (qval0_2 ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "q_val" ) ) (j + 1) 1001)
  ** (intArray.seg ( &( "q_idx" ) ) (0 : Int) (j + 1) (qidx0_2 ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "q_idx" ) ) (j + 1) 1001)
  ** (intArray.seg ( &( "old" ) ) (0 : Int) (j + 1) (old0_2 ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "old" ) ) (j + 1) 1001)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) (j + 1) (dp_l_2 ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "dp" ) ) (j + 1) 1001)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
|--
  EX qval0 : (List Int), EX qidx0 : (List Int), EX old0 : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (j + 1)) ” &&
  “ ((Zlength (old0)) = (j + 1)) ” &&
  “ ((Zlength (qidx0)) = (j + 1)) ” &&
  “ ((Zlength (qval0)) = (j + 1)) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (capacity_pre + 1)) ” &&
  “ (Forall (Eq ((0 : Int))) dp_l) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) (j + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (j + 1) 1001)
  ** (intArray.seg ( &( "old" ) ) (0 : Int) (j + 1) old0)
  ** (intArray.undef_seg ( &( "old" ) ) (j + 1) 1001)
  ** (intArray.seg ( &( "q_idx" ) ) (0 : Int) (j + 1) qidx0)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (j + 1) 1001)
  ** (intArray.seg ( &( "q_val" ) ) (0 : Int) (j + 1) qval0)
  ** (intArray.undef_seg ( &( "q_val" ) ) (j + 1) 1001)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (qval0_2 : (List Int)) (qidx0_2 : (List Int)) (old0_2 : (List Int)) (j : Int) (dp_l_2 : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = j)) (PreH10 : ((Zlength (old0_2)) = j)) (PreH11 : ((Zlength (qidx0_2)) = j)) (PreH12 : ((Zlength (qval0_2)) = j)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= (capacity_pre + 1))) (PreH15 : (Forall (Eq ((0 : Int))) dp_l_2)) (PreH16 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH17 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  TT && emp 
|--
  “ (Forall (Eq ((0 : Int))) (dp_l_2 ++ ((0 : Int) :: (@List.nil Int)))) ” &&
  “ ((Zlength ((qval0_2 ++ ((0 : Int) :: (@List.nil Int))))) = (j + 1)) ” &&
  “ ((Zlength ((qidx0_2 ++ ((0 : Int) :: (@List.nil Int))))) = (j + 1)) ” &&
  “ ((Zlength ((old0_2 ++ ((0 : Int) :: (@List.nil Int))))) = (j + 1)) ” &&
  “ ((Zlength ((dp_l_2 ++ ((0 : Int) :: (@List.nil Int))))) = (j + 1)) ”
  &&  emp
)

noncomputable def multipleKnapsack_entail_wit_2_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (qval0_2 : (List Int)) (qidx0_2 : (List Int)) (old0_2 : (List Int)) (j : Int) (dp_l_2 : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = j)) (PreH10 : ((Zlength (old0_2)) = j)) (PreH11 : ((Zlength (qidx0_2)) = j)) (PreH12 : ((Zlength (qval0_2)) = j)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= (capacity_pre + 1))) (PreH15 : (Forall (Eq ((0 : Int))) dp_l_2)) (PreH16 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH17 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (Forall (Eq ((0 : Int))) (dp_l_2 ++ ((0 : Int) :: (@List.nil Int))))

noncomputable def multipleKnapsack_entail_wit_2_split_goal_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (qval0_2 : (List Int)) (qidx0_2 : (List Int)) (old0_2 : (List Int)) (j : Int) (dp_l_2 : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = j)) (PreH10 : ((Zlength (old0_2)) = j)) (PreH11 : ((Zlength (qidx0_2)) = j)) (PreH12 : ((Zlength (qval0_2)) = j)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= (capacity_pre + 1))) (PreH15 : (Forall (Eq ((0 : Int))) dp_l_2)) (PreH16 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH17 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  ((Zlength ((qval0_2 ++ ((0 : Int) :: (@List.nil Int))))) = (j + 1))

noncomputable def multipleKnapsack_entail_wit_2_split_goal_3 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (qval0_2 : (List Int)) (qidx0_2 : (List Int)) (old0_2 : (List Int)) (j : Int) (dp_l_2 : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = j)) (PreH10 : ((Zlength (old0_2)) = j)) (PreH11 : ((Zlength (qidx0_2)) = j)) (PreH12 : ((Zlength (qval0_2)) = j)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= (capacity_pre + 1))) (PreH15 : (Forall (Eq ((0 : Int))) dp_l_2)) (PreH16 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH17 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  ((Zlength ((qidx0_2 ++ ((0 : Int) :: (@List.nil Int))))) = (j + 1))

noncomputable def multipleKnapsack_entail_wit_2_split_goal_4 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (qval0_2 : (List Int)) (qidx0_2 : (List Int)) (old0_2 : (List Int)) (j : Int) (dp_l_2 : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = j)) (PreH10 : ((Zlength (old0_2)) = j)) (PreH11 : ((Zlength (qidx0_2)) = j)) (PreH12 : ((Zlength (qval0_2)) = j)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= (capacity_pre + 1))) (PreH15 : (Forall (Eq ((0 : Int))) dp_l_2)) (PreH16 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH17 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  ((Zlength ((old0_2 ++ ((0 : Int) :: (@List.nil Int))))) = (j + 1))

noncomputable def multipleKnapsack_entail_wit_2_split_goal_5 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (qval0_2 : (List Int)) (qidx0_2 : (List Int)) (old0_2 : (List Int)) (j : Int) (dp_l_2 : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = j)) (PreH10 : ((Zlength (old0_2)) = j)) (PreH11 : ((Zlength (qidx0_2)) = j)) (PreH12 : ((Zlength (qval0_2)) = j)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= (capacity_pre + 1))) (PreH15 : (Forall (Eq ((0 : Int))) dp_l_2)) (PreH16 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH17 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  ((Zlength ((dp_l_2 ++ ((0 : Int) :: (@List.nil Int))))) = (j + 1))

noncomputable def multipleKnapsack_entail_wit_3 : Prop :=
  (
forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (qval0 : (List Int)) (qidx0 : (List Int)) (old0 : (List Int)) (j : Int) (dp_l_2 : (List Int)) (PreH1 : (j > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = j)) (PreH10 : ((Zlength (old0)) = j)) (PreH11 : ((Zlength (qidx0)) = j)) (PreH12 : ((Zlength (qval0)) = j)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= (capacity_pre + 1))) (PreH15 : (Forall (Eq ((0 : Int))) dp_l_2)) (PreH16 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH17 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) j dp_l_2)
  ** (intArray.undef_seg ( &( "dp" ) ) j 1001)
  ** (intArray.seg ( &( "old" ) ) (0 : Int) j old0)
  ** (intArray.undef_seg ( &( "old" ) ) j 1001)
  ** (intArray.seg ( &( "q_idx" ) ) (0 : Int) j qidx0)
  ** (intArray.undef_seg ( &( "q_idx" ) ) j 1001)
  ** (intArray.seg ( &( "q_val" ) ) (0 : Int) j qval0)
  ** (intArray.undef_seg ( &( "q_val" ) ) j 1001)
|--
  EX qval_l : (List Int), EX qidx_l : (List Int), EX old_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l (0 : Int) capacity_pre dp_l) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (qval0 : (List Int)) (qidx0 : (List Int)) (old0 : (List Int)) (j : Int) (dp_l_2 : (List Int)) (PreH1 : (j > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = j)) (PreH10 : ((Zlength (old0)) = j)) (PreH11 : ((Zlength (qidx0)) = j)) (PreH12 : ((Zlength (qval0)) = j)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= (capacity_pre + 1))) (PreH15 : (Forall (Eq ((0 : Int))) dp_l_2)) (PreH16 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH17 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.seg ( &( "dp" ) ) (0 : Int) j dp_l_2)
  ** (intArray.seg ( &( "old" ) ) (0 : Int) j old0)
  ** (intArray.seg ( &( "q_idx" ) ) (0 : Int) j qidx0)
  ** (intArray.seg ( &( "q_val" ) ) (0 : Int) j qval0)
|--
  EX qval_l : (List Int), EX qidx_l : (List Int), EX old_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l (0 : Int) capacity_pre dp_l) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
)

noncomputable def multipleKnapsack_entail_wit_4 : Prop :=
  (
forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH16 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH17 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l_2)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l_2)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l_2)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l_2)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  EX qval_l : (List Int), EX qidx_l : (List Int), EX old_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l) ” &&
  “ (MKCopyPrefixSemantics dp_l old_l (0 : Int)) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH16 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH17 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  TT && emp 
|--
  “ (MKCopyPrefixSemantics dp_l_2 old_l_2 (0 : Int)) ”
  &&  emp
)

noncomputable def multipleKnapsack_entail_wit_4_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH16 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH17 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (MKCopyPrefixSemantics dp_l_2 old_l_2 (0 : Int))

noncomputable def multipleKnapsack_entail_wit_5 : Prop :=
  (
forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH18 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j)) (PreH19 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH20 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH22 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH23 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH24 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "old" ) ) (capacity_pre + 1) (replace_Znth (j) ((Znth j dp_l_2 (0 : Int))) (old_l_2)))
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l_2)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l_2)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l_2)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  EX qval_l : (List Int), EX qidx_l : (List Int), EX old_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l) ” &&
  “ (MKCopyPrefixSemantics dp_l old_l (j + 1)) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH18 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j)) (PreH19 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH20 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH22 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH23 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH24 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  TT && emp 
|--
  “ (MKCopyPrefixSemantics dp_l_2 (replace_Znth (j) ((Znth j dp_l_2 (0 : Int))) (old_l_2)) (j + 1)) ” &&
  “ ((Zlength ((replace_Znth (j) ((Znth j dp_l_2 (0 : Int))) (old_l_2)))) = (capacity_pre + 1)) ”
  &&  emp
)

noncomputable def multipleKnapsack_entail_wit_5_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH18 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j)) (PreH19 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH20 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH22 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH23 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH24 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (MKCopyPrefixSemantics dp_l_2 (replace_Znth (j) ((Znth j dp_l_2 (0 : Int))) (old_l_2)) (j + 1))

noncomputable def multipleKnapsack_entail_wit_5_split_goal_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH18 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j)) (PreH19 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH20 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH22 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH23 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH24 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  ((Zlength ((replace_Znth (j) ((Znth j dp_l_2 (0 : Int))) (old_l_2)))) = (capacity_pre + 1))

noncomputable def multipleKnapsack_entail_wit_6 : Prop :=
  (
forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (j > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH18 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j)) (PreH19 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH20 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH22 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH23 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH24 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l_2)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l_2)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l_2)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l_2)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  EX qval_l : (List Int), EX qidx_l : (List Int), EX old_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((Znth i weights_l (0 : Int)) = (Znth i weights_l (0 : Int))) ” &&
  “ ((Znth i values_l (0 : Int)) = (Znth i values_l (0 : Int))) ” &&
  “ ((Znth i counts_l (0 : Int)) = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= (Znth i weights_l (0 : Int))) ” &&
  “ ((Znth i weights_l (0 : Int)) <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= (Znth i values_l (0 : Int))) ” &&
  “ ((Znth i values_l (0 : Int)) <= 1000) ” &&
  “ ((0 : Int) <= (Znth i counts_l (0 : Int))) ” &&
  “ ((Znth i counts_l (0 : Int)) <= capacity_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (Znth i weights_l (0 : Int))) ” &&
  “ ((0 : Int) <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) old_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000000)) old_l) ” &&
  “ forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l (Znth i weights_l (0 : Int)) (Znth i values_l (0 : Int)) (Znth i counts_l (0 : Int)) capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000))) ” &&
  “ (MKItemResidueProgressSemantics old_l dp_l (0 : Int) (Znth i weights_l (0 : Int)) (Znth i values_l (0 : Int)) (Znth i counts_l (0 : Int)) capacity_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (j > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH18 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j)) (PreH19 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH20 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH22 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH23 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH24 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  TT && emp 
|--
  “ (MKItemResidueProgressSemantics old_l_2 dp_l_2 (0 : Int) (Znth i weights_l (0 : Int)) (Znth i values_l (0 : Int)) (Znth i counts_l (0 : Int)) capacity_pre) ” &&
  “ forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 (Znth i weights_l (0 : Int)) (Znth i values_l (0 : Int)) (Znth i counts_l (0 : Int)) capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000))) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000000)) old_l_2) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2) ” &&
  “ ((0 : Int) <= (Znth i weights_l (0 : Int))) ” &&
  “ ((Znth i counts_l (0 : Int)) <= capacity_pre) ” &&
  “ ((0 : Int) <= (Znth i counts_l (0 : Int))) ” &&
  “ ((Znth i values_l (0 : Int)) <= 1000) ” &&
  “ ((0 : Int) <= (Znth i values_l (0 : Int))) ” &&
  “ ((Znth i weights_l (0 : Int)) <= (capacity_pre + 1)) ” &&
  “ (1 <= (Znth i weights_l (0 : Int))) ”
  &&  emp
)

noncomputable def multipleKnapsack_entail_wit_6_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (j > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH18 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j)) (PreH19 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH20 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH22 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH23 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH24 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (MKItemResidueProgressSemantics old_l_2 dp_l_2 (0 : Int) (Znth i weights_l (0 : Int)) (Znth i values_l (0 : Int)) (Znth i counts_l (0 : Int)) capacity_pre)

noncomputable def multipleKnapsack_entail_wit_6_split_goal_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (j > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH18 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j)) (PreH19 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH20 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH22 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH23 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH24 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 (Znth i weights_l (0 : Int)) (Znth i values_l (0 : Int)) (Znth i counts_l (0 : Int)) capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))

noncomputable def multipleKnapsack_entail_wit_6_split_goal_3 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (j > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH18 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j)) (PreH19 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH20 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH22 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH23 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH24 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)

noncomputable def multipleKnapsack_entail_wit_6_split_goal_4 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (j > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH18 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j)) (PreH19 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH20 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH22 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH23 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH24 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)

noncomputable def multipleKnapsack_entail_wit_6_split_goal_5 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (j > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH18 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j)) (PreH19 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH20 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH22 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH23 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH24 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)

noncomputable def multipleKnapsack_entail_wit_6_split_goal_6 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (j > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH18 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j)) (PreH19 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH20 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH22 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH23 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH24 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  ((0 : Int) <= (Znth i weights_l (0 : Int)))

noncomputable def multipleKnapsack_entail_wit_6_split_goal_7 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (j > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH18 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j)) (PreH19 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH20 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH22 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH23 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH24 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  ((Znth i counts_l (0 : Int)) <= capacity_pre)

noncomputable def multipleKnapsack_entail_wit_6_split_goal_8 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (j > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH18 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j)) (PreH19 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH20 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH22 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH23 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH24 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  ((0 : Int) <= (Znth i counts_l (0 : Int)))

noncomputable def multipleKnapsack_entail_wit_6_split_goal_9 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (j > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH18 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j)) (PreH19 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH20 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH22 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH23 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH24 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  ((Znth i values_l (0 : Int)) <= 1000)

noncomputable def multipleKnapsack_entail_wit_6_split_goal_10 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (j > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH18 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j)) (PreH19 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH20 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH22 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH23 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH24 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  ((0 : Int) <= (Znth i values_l (0 : Int)))

noncomputable def multipleKnapsack_entail_wit_6_split_goal_11 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (j > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH18 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j)) (PreH19 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH20 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH22 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH23 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH24 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  ((Znth i weights_l (0 : Int)) <= (capacity_pre + 1))

noncomputable def multipleKnapsack_entail_wit_6_split_goal_12 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (j > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2)) (PreH18 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j)) (PreH19 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH20 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH22 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH23 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH24 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (1 <= (Znth i weights_l (0 : Int)))

noncomputable def multipleKnapsack_entail_wit_7 : Prop :=
  (
forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (r : Int) (cnt : Int) (v : Int) (w : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (r <= capacity_pre)) (PreH2 : (r < w)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : (w = (Znth i weights_l (0 : Int)))) (PreH17 : (v = (Znth i values_l (0 : Int)))) (PreH18 : (cnt = (Znth i counts_l (0 : Int)))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1))) (PreH21 : ((0 : Int) <= v)) (PreH22 : (v <= 1000)) (PreH23 : ((0 : Int) <= cnt)) (PreH24 : (cnt <= capacity_pre)) (PreH25 : ((0 : Int) <= r)) (PreH26 : (r <= w)) (PreH27 : (r <= (capacity_pre + 1))) (PreH28 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH30 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH31 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH32 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 r w v cnt capacity_pre)) (PreH33 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH34 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l_2)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l_2)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l_2)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l_2)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  EX qval_l : (List Int), EX qidx_l : (List Int), EX old_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ (r = (r + ((0 : Int) * w))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r <= (capacity_pre + w)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) old_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000000)) old_l) ” &&
  “ forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000))) ” &&
  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt (0 : Int) capacity_pre) ” &&
  “ (MKQueueResultSemantics old_l qidx_l qval_l (0 : Int) (0 : Int) r w v cnt (0 : Int) capacity_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((-(((0 : Int) - 1) * v)))) (sublist ((0 : Int)) ((0 : Int)) (qval_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) ((1000000 - (((0 : Int) - 1) * v)))) (sublist ((0 : Int)) ((0 : Int)) (qval_l))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (r : Int) (cnt : Int) (v : Int) (w : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (r <= capacity_pre)) (PreH2 : (r < w)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : (w = (Znth i weights_l (0 : Int)))) (PreH17 : (v = (Znth i values_l (0 : Int)))) (PreH18 : (cnt = (Znth i counts_l (0 : Int)))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1))) (PreH21 : ((0 : Int) <= v)) (PreH22 : (v <= 1000)) (PreH23 : ((0 : Int) <= cnt)) (PreH24 : (cnt <= capacity_pre)) (PreH25 : ((0 : Int) <= r)) (PreH26 : (r <= w)) (PreH27 : (r <= (capacity_pre + 1))) (PreH28 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH30 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH31 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH32 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 r w v cnt capacity_pre)) (PreH33 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH34 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  TT && emp 
|--
  “ (Forall ((GE.ge (α := Int)) ((1000000 - (((0 : Int) - 1) * v)))) (sublist ((0 : Int)) ((0 : Int)) (qval_l_2))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-(((0 : Int) - 1) * v)))) (sublist ((0 : Int)) ((0 : Int)) (qval_l_2))) ” &&
  “ (MKQueueResultSemantics old_l_2 qidx_l_2 qval_l_2 (0 : Int) (0 : Int) r w v cnt (0 : Int) capacity_pre) ” &&
  “ (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt (0 : Int) capacity_pre) ” &&
  “ forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000))) ”
  &&  emp
)

noncomputable def multipleKnapsack_entail_wit_7_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (r : Int) (cnt : Int) (v : Int) (w : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (r <= capacity_pre)) (PreH2 : (r < w)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : (w = (Znth i weights_l (0 : Int)))) (PreH17 : (v = (Znth i values_l (0 : Int)))) (PreH18 : (cnt = (Znth i counts_l (0 : Int)))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1))) (PreH21 : ((0 : Int) <= v)) (PreH22 : (v <= 1000)) (PreH23 : ((0 : Int) <= cnt)) (PreH24 : (cnt <= capacity_pre)) (PreH25 : ((0 : Int) <= r)) (PreH26 : (r <= w)) (PreH27 : (r <= (capacity_pre + 1))) (PreH28 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH30 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH31 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH32 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 r w v cnt capacity_pre)) (PreH33 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH34 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (Forall ((GE.ge (α := Int)) ((1000000 - (((0 : Int) - 1) * v)))) (sublist ((0 : Int)) ((0 : Int)) (qval_l_2)))

noncomputable def multipleKnapsack_entail_wit_7_split_goal_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (r : Int) (cnt : Int) (v : Int) (w : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (r <= capacity_pre)) (PreH2 : (r < w)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : (w = (Znth i weights_l (0 : Int)))) (PreH17 : (v = (Znth i values_l (0 : Int)))) (PreH18 : (cnt = (Znth i counts_l (0 : Int)))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1))) (PreH21 : ((0 : Int) <= v)) (PreH22 : (v <= 1000)) (PreH23 : ((0 : Int) <= cnt)) (PreH24 : (cnt <= capacity_pre)) (PreH25 : ((0 : Int) <= r)) (PreH26 : (r <= w)) (PreH27 : (r <= (capacity_pre + 1))) (PreH28 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH30 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH31 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH32 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 r w v cnt capacity_pre)) (PreH33 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH34 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (Forall ((LE.le (α := Int)) ((-(((0 : Int) - 1) * v)))) (sublist ((0 : Int)) ((0 : Int)) (qval_l_2)))

noncomputable def multipleKnapsack_entail_wit_7_split_goal_3 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (r : Int) (cnt : Int) (v : Int) (w : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (r <= capacity_pre)) (PreH2 : (r < w)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : (w = (Znth i weights_l (0 : Int)))) (PreH17 : (v = (Znth i values_l (0 : Int)))) (PreH18 : (cnt = (Znth i counts_l (0 : Int)))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1))) (PreH21 : ((0 : Int) <= v)) (PreH22 : (v <= 1000)) (PreH23 : ((0 : Int) <= cnt)) (PreH24 : (cnt <= capacity_pre)) (PreH25 : ((0 : Int) <= r)) (PreH26 : (r <= w)) (PreH27 : (r <= (capacity_pre + 1))) (PreH28 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH30 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH31 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH32 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 r w v cnt capacity_pre)) (PreH33 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH34 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (MKQueueResultSemantics old_l_2 qidx_l_2 qval_l_2 (0 : Int) (0 : Int) r w v cnt (0 : Int) capacity_pre)

noncomputable def multipleKnapsack_entail_wit_7_split_goal_4 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (r : Int) (cnt : Int) (v : Int) (w : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (r <= capacity_pre)) (PreH2 : (r < w)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : (w = (Znth i weights_l (0 : Int)))) (PreH17 : (v = (Znth i values_l (0 : Int)))) (PreH18 : (cnt = (Znth i counts_l (0 : Int)))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1))) (PreH21 : ((0 : Int) <= v)) (PreH22 : (v <= 1000)) (PreH23 : ((0 : Int) <= cnt)) (PreH24 : (cnt <= capacity_pre)) (PreH25 : ((0 : Int) <= r)) (PreH26 : (r <= w)) (PreH27 : (r <= (capacity_pre + 1))) (PreH28 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH30 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH31 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH32 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 r w v cnt capacity_pre)) (PreH33 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH34 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt (0 : Int) capacity_pre)

noncomputable def multipleKnapsack_entail_wit_7_split_goal_5 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (r : Int) (cnt : Int) (v : Int) (w : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (r <= capacity_pre)) (PreH2 : (r < w)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : (w = (Znth i weights_l (0 : Int)))) (PreH17 : (v = (Znth i values_l (0 : Int)))) (PreH18 : (cnt = (Znth i counts_l (0 : Int)))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1))) (PreH21 : ((0 : Int) <= v)) (PreH22 : (v <= 1000)) (PreH23 : ((0 : Int) <= cnt)) (PreH24 : (cnt <= capacity_pre)) (PreH25 : ((0 : Int) <= r)) (PreH26 : (r <= w)) (PreH27 : (r <= (capacity_pre + 1))) (PreH28 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH29 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH30 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH31 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH32 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 r w v cnt capacity_pre)) (PreH33 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH34 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))

noncomputable def multipleKnapsack_entail_wit_8 : Prop :=
  (
forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (pos <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH39 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l dp_l_2 r w v cnt k capacity_pre)) (PreH41 : (MKQueueResultSemantics old_l qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre)) (PreH42 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH43 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH44 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH45 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH46 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH48 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH49 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l_2)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l_2)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l_2)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  EX qval_l : (List Int), EX qidx_l : (List Int), EX old_l_2 : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l_2)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ (pos = (r + (k * w))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= capacity_pre) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= capacity_pre) ” &&
  “ (((Znth pos old_l (0 : Int)) - (k * v)) = ((Znth pos old_l_2 (0 : Int)) - (k * v))) ” &&
  “ ((-1000000) <= ((Znth pos old_l (0 : Int)) - (k * v))) ” &&
  “ (((Znth pos old_l (0 : Int)) - (k * v)) <= 1000000) ” &&
  “ ((0 : Int) <= (((Znth pos old_l (0 : Int)) - (k * v)) + (k * v))) ” &&
  “ ((((Znth pos old_l (0 : Int)) - (k * v)) + (k * v)) <= 1000000) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= k) ” &&
  “ (tail <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000000)) old_l_2) ” &&
  “ forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000))) ” &&
  “ (MKItemResiduePrefixSemantics old_l_2 dp_l r w v cnt k capacity_pre) ” &&
  “ (MKQueueDropSemantics old_l_2 qidx_l qval_l head tail r w v cnt k) ” &&
  “ (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l_2)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (pos <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH39 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l dp_l_2 r w v cnt k capacity_pre)) (PreH41 : (MKQueueResultSemantics old_l qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre)) (PreH42 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH43 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH44 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH45 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH46 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH48 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH49 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  TT && emp 
|--
  “ (MKQueueDropSemantics old_l qidx_l_2 qval_l_2 head tail r w v cnt k) ” &&
  “ forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000))) ” &&
  “ ((((Znth (r + (k * w)) old_l (0 : Int)) - (k * v)) + (k * v)) <= 1000000) ” &&
  “ ((0 : Int) <= (((Znth (r + (k * w)) old_l (0 : Int)) - (k * v)) + (k * v))) ” &&
  “ (((Znth (r + (k * w)) old_l (0 : Int)) - (k * v)) <= 1000000) ” &&
  “ ((-1000000) <= ((Znth (r + (k * w)) old_l (0 : Int)) - (k * v))) ”
  &&  emp
)

noncomputable def multipleKnapsack_entail_wit_8_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (pos <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH39 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l dp_l_2 r w v cnt k capacity_pre)) (PreH41 : (MKQueueResultSemantics old_l qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre)) (PreH42 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH43 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH44 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH45 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH46 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH48 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH49 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (MKQueueDropSemantics old_l qidx_l_2 qval_l_2 head tail r w v cnt k)

noncomputable def multipleKnapsack_entail_wit_8_split_goal_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (pos <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH39 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l dp_l_2 r w v cnt k capacity_pre)) (PreH41 : (MKQueueResultSemantics old_l qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre)) (PreH42 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH43 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH44 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH45 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH46 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH48 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH49 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))

noncomputable def multipleKnapsack_entail_wit_8_split_goal_3 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (pos <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH39 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l dp_l_2 r w v cnt k capacity_pre)) (PreH41 : (MKQueueResultSemantics old_l qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre)) (PreH42 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH43 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH44 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH45 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH46 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH48 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH49 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  ((((Znth (r + (k * w)) old_l (0 : Int)) - (k * v)) + (k * v)) <= 1000000)

noncomputable def multipleKnapsack_entail_wit_8_split_goal_4 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (pos <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH39 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l dp_l_2 r w v cnt k capacity_pre)) (PreH41 : (MKQueueResultSemantics old_l qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre)) (PreH42 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH43 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH44 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH45 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH46 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH48 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH49 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  ((0 : Int) <= (((Znth (r + (k * w)) old_l (0 : Int)) - (k * v)) + (k * v)))

noncomputable def multipleKnapsack_entail_wit_8_split_goal_5 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (pos <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH39 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l dp_l_2 r w v cnt k capacity_pre)) (PreH41 : (MKQueueResultSemantics old_l qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre)) (PreH42 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH43 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH44 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH45 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH46 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH48 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH49 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (((Znth (r + (k * w)) old_l (0 : Int)) - (k * v)) <= 1000000)

noncomputable def multipleKnapsack_entail_wit_8_split_goal_6 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (pos <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH39 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l dp_l_2 r w v cnt k capacity_pre)) (PreH41 : (MKQueueResultSemantics old_l qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre)) (PreH42 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH43 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH44 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH45 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH46 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH48 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH49 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  ((-1000000) <= ((Znth (r + (k * w)) old_l (0 : Int)) - (k * v)))

noncomputable def multipleKnapsack_entail_wit_9 : Prop :=
  (
forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth head qidx_l_2 (0 : Int)) < (k - cnt))) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH45 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH47 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k)) (PreH48 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l_2)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l_2)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l_2)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l_2)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  EX qval_l : (List Int), EX qidx_l : (List Int), EX old_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ (pos = (r + (k * w))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= capacity_pre) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= capacity_pre) ” &&
  “ (current = ((Znth pos old_l (0 : Int)) - (k * v))) ” &&
  “ ((-1000000) <= current) ” &&
  “ (current <= 1000000) ” &&
  “ ((0 : Int) <= (current + (k * v))) ” &&
  “ ((current + (k * v)) <= 1000000) ” &&
  “ ((0 : Int) <= (head + 1)) ” &&
  “ ((head + 1) <= tail) ” &&
  “ (tail <= k) ” &&
  “ (tail <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) old_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000000)) old_l) ” &&
  “ forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000))) ” &&
  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre) ” &&
  “ (MKQueueDropSemantics old_l qidx_l qval_l (head + 1) tail r w v cnt k) ” &&
  “ (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist ((head + 1)) (tail) (qval_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist ((head + 1)) (tail) (qval_l))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth head qidx_l_2 (0 : Int)) < (k - cnt))) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH45 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH47 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k)) (PreH48 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  TT && emp 
|--
  “ (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist ((head + 1)) (tail) (qval_l_2))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist ((head + 1)) (tail) (qval_l_2))) ” &&
  “ (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 (head + 1) tail r w v cnt k) ”
  &&  emp
)

noncomputable def multipleKnapsack_entail_wit_9_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth head qidx_l_2 (0 : Int)) < (k - cnt))) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH45 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH47 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k)) (PreH48 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist ((head + 1)) (tail) (qval_l_2)))

noncomputable def multipleKnapsack_entail_wit_9_split_goal_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth head qidx_l_2 (0 : Int)) < (k - cnt))) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH45 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH47 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k)) (PreH48 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist ((head + 1)) (tail) (qval_l_2)))

noncomputable def multipleKnapsack_entail_wit_9_split_goal_3 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth head qidx_l_2 (0 : Int)) < (k - cnt))) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH45 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH47 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k)) (PreH48 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 (head + 1) tail r w v cnt k)

noncomputable def multipleKnapsack_entail_wit_10_1 : Prop :=
  (
forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH42 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH44 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH46 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k)) (PreH47 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH48 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH50 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH52 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH54 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l_2)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l_2)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l_2)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l_2)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  EX qval_l : (List Int), EX qidx_l : (List Int), EX old_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ (pos = (r + (k * w))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= capacity_pre) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= capacity_pre) ” &&
  “ (current = ((Znth pos old_l (0 : Int)) - (k * v))) ” &&
  “ ((-1000000) <= current) ” &&
  “ (current <= 1000000) ” &&
  “ ((0 : Int) <= (current + (k * v))) ” &&
  “ ((current + (k * v)) <= 1000000) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= k) ” &&
  “ (tail <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) old_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000000)) old_l) ” &&
  “ forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000))) ” &&
  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre) ” &&
  “ (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current) ” &&
  “ (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH42 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH44 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH46 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k)) (PreH47 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH48 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH50 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH52 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH54 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  TT && emp 
|--
  “ (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l_2))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l_2))) ” &&
  “ (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current) ” &&
  “ forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000))) ”
  &&  emp
)

noncomputable def multipleKnapsack_entail_wit_10_1_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH42 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH44 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH46 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k)) (PreH47 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH48 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH50 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH52 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH54 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l_2)))

noncomputable def multipleKnapsack_entail_wit_10_1_split_goal_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH42 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH44 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH46 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k)) (PreH47 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH48 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH50 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH52 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH54 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l_2)))

noncomputable def multipleKnapsack_entail_wit_10_1_split_goal_3 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH42 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH44 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH46 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k)) (PreH47 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH48 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH50 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH52 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH54 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)

noncomputable def multipleKnapsack_entail_wit_10_1_split_goal_4 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH42 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH44 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH46 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k)) (PreH47 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH48 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH50 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH52 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH54 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))

noncomputable def multipleKnapsack_entail_wit_10_2 : Prop :=
  (
forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth head qidx_l_2 (0 : Int)) >= (k - cnt))) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH45 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH47 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k)) (PreH48 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l_2)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l_2)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l_2)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l_2)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  EX qval_l : (List Int), EX qidx_l : (List Int), EX old_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ (pos = (r + (k * w))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= capacity_pre) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= capacity_pre) ” &&
  “ (current = ((Znth pos old_l (0 : Int)) - (k * v))) ” &&
  “ ((-1000000) <= current) ” &&
  “ (current <= 1000000) ” &&
  “ ((0 : Int) <= (current + (k * v))) ” &&
  “ ((current + (k * v)) <= 1000000) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= k) ” &&
  “ (tail <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) old_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000000)) old_l) ” &&
  “ forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000))) ” &&
  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre) ” &&
  “ (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current) ” &&
  “ (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth head qidx_l_2 (0 : Int)) >= (k - cnt))) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH45 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH47 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k)) (PreH48 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  TT && emp 
|--
  “ (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l_2))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l_2))) ” &&
  “ (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current) ” &&
  “ forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000))) ”
  &&  emp
)

noncomputable def multipleKnapsack_entail_wit_10_2_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth head qidx_l_2 (0 : Int)) >= (k - cnt))) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH45 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH47 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k)) (PreH48 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l_2)))

noncomputable def multipleKnapsack_entail_wit_10_2_split_goal_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth head qidx_l_2 (0 : Int)) >= (k - cnt))) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH45 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH47 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k)) (PreH48 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l_2)))

noncomputable def multipleKnapsack_entail_wit_10_2_split_goal_3 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth head qidx_l_2 (0 : Int)) >= (k - cnt))) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH45 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH47 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k)) (PreH48 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)

noncomputable def multipleKnapsack_entail_wit_10_2_split_goal_4 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth head qidx_l_2 (0 : Int)) >= (k - cnt))) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH45 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH47 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k)) (PreH48 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))

noncomputable def multipleKnapsack_entail_wit_11 : Prop :=
  (
forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l_2 (0 : Int)) <= current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH45 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH47 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH48 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l_2)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l_2)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l_2)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l_2)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  EX qval_l : (List Int), EX qidx_l : (List Int), EX old_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ (pos = (r + (k * w))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= capacity_pre) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= capacity_pre) ” &&
  “ (current = ((Znth pos old_l (0 : Int)) - (k * v))) ” &&
  “ ((-1000000) <= current) ” &&
  “ (current <= 1000000) ” &&
  “ ((0 : Int) <= (current + (k * v))) ” &&
  “ ((current + (k * v)) <= 1000000) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= (tail - 1)) ” &&
  “ ((tail - 1) <= k) ” &&
  “ ((tail - 1) <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) old_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000000)) old_l) ” &&
  “ forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000))) ” &&
  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre) ” &&
  “ (MKQueuePendingSemantics old_l qidx_l qval_l head (tail - 1) r w v cnt k current) ” &&
  “ (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) ((tail - 1)) (qval_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) ((tail - 1)) (qval_l))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l_2 (0 : Int)) <= current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH45 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH47 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH48 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  TT && emp 
|--
  “ (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) ((tail - 1)) (qval_l_2))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) ((tail - 1)) (qval_l_2))) ” &&
  “ (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head (tail - 1) r w v cnt k current) ”
  &&  emp
)

noncomputable def multipleKnapsack_entail_wit_11_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l_2 (0 : Int)) <= current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH45 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH47 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH48 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) ((tail - 1)) (qval_l_2)))

noncomputable def multipleKnapsack_entail_wit_11_split_goal_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l_2 (0 : Int)) <= current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH45 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH47 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH48 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) ((tail - 1)) (qval_l_2)))

noncomputable def multipleKnapsack_entail_wit_11_split_goal_3 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l_2 (0 : Int)) <= current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH45 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH47 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH48 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head (tail - 1) r w v cnt k current)

noncomputable def multipleKnapsack_entail_wit_12_1 : Prop :=
  (
forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH42 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH44 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH46 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH47 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH48 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH50 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH52 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH54 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "dp" ) ) (capacity_pre + 1) (replace_Znth (pos) (((Znth head (replace_Znth (tail) (current) (qval_l_2)) (0 : Int)) + (k * v))) (dp_l_2)))
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) (replace_Znth (tail) (current) (qval_l_2)))
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l_2)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l_2)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  EX qval_l : (List Int), EX qidx_l : (List Int), EX old_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ ((pos + w) = (r + ((k + 1) * w))) ” &&
  “ ((0 : Int) <= (k + 1)) ” &&
  “ ((k + 1) <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= (pos + w)) ” &&
  “ ((pos + w) <= (capacity_pre + w)) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= (tail + 1)) ” &&
  “ ((tail + 1) <= (k + 1)) ” &&
  “ ((tail + 1) <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) old_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000000)) old_l) ” &&
  “ forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000))) ” &&
  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt (k + 1) capacity_pre) ” &&
  “ (MKQueueResultSemantics old_l qidx_l qval_l head (tail + 1) r w v cnt (k + 1) capacity_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((-(((k + 1) - 1) * v)))) (sublist (head) ((tail + 1)) (qval_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) ((1000000 - (((k + 1) - 1) * v)))) (sublist (head) ((tail + 1)) (qval_l))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH42 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH44 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH46 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH47 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH48 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH50 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH52 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH54 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  TT && emp 
|--
  “ (Forall ((GE.ge (α := Int)) ((1000000 - (((k + 1) - 1) * v)))) (sublist (head) ((tail + 1)) ((replace_Znth (tail) (current) (qval_l_2))))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-(((k + 1) - 1) * v)))) (sublist (head) ((tail + 1)) ((replace_Znth (tail) (current) (qval_l_2))))) ” &&
  “ (MKQueueResultSemantics old_l_2 (replace_Znth (tail) (k) (qidx_l_2)) (replace_Znth (tail) (current) (qval_l_2)) head (tail + 1) r w v cnt (k + 1) capacity_pre) ” &&
  “ (MKItemResiduePrefixSemantics old_l_2 (replace_Znth ((r + (k * w))) (((Znth head (replace_Znth (tail) (current) (qval_l_2)) (0 : Int)) + (k * v))) (dp_l_2)) r w v cnt (k + 1) capacity_pre) ” &&
  “ forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000))) ” &&
  “ (((r + (k * w)) + w) = (r + ((k + 1) * w))) ” &&
  “ ((Zlength ((replace_Znth (tail) (current) (qval_l_2)))) = (capacity_pre + 1)) ” &&
  “ ((Zlength ((replace_Znth (tail) (k) (qidx_l_2)))) = (capacity_pre + 1)) ” &&
  “ ((Zlength ((replace_Znth ((r + (k * w))) (((Znth head (replace_Znth (tail) (current) (qval_l_2)) (0 : Int)) + (k * v))) (dp_l_2)))) = (capacity_pre + 1)) ”
  &&  emp
)

noncomputable def multipleKnapsack_entail_wit_12_1_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH42 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH44 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH46 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH47 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH48 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH50 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH52 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH54 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (Forall ((GE.ge (α := Int)) ((1000000 - (((k + 1) - 1) * v)))) (sublist (head) ((tail + 1)) ((replace_Znth (tail) (current) (qval_l_2)))))

noncomputable def multipleKnapsack_entail_wit_12_1_split_goal_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH42 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH44 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH46 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH47 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH48 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH50 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH52 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH54 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (Forall ((LE.le (α := Int)) ((-(((k + 1) - 1) * v)))) (sublist (head) ((tail + 1)) ((replace_Znth (tail) (current) (qval_l_2)))))

noncomputable def multipleKnapsack_entail_wit_12_1_split_goal_3 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH42 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH44 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH46 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH47 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH48 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH50 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH52 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH54 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (MKQueueResultSemantics old_l_2 (replace_Znth (tail) (k) (qidx_l_2)) (replace_Znth (tail) (current) (qval_l_2)) head (tail + 1) r w v cnt (k + 1) capacity_pre)

noncomputable def multipleKnapsack_entail_wit_12_1_split_goal_4 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH42 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH44 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH46 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH47 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH48 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH50 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH52 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH54 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (MKItemResiduePrefixSemantics old_l_2 (replace_Znth ((r + (k * w))) (((Znth head (replace_Znth (tail) (current) (qval_l_2)) (0 : Int)) + (k * v))) (dp_l_2)) r w v cnt (k + 1) capacity_pre)

noncomputable def multipleKnapsack_entail_wit_12_1_split_goal_5 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH42 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH44 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH46 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH47 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH48 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH50 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH52 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH54 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))

noncomputable def multipleKnapsack_entail_wit_12_1_split_goal_6 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH42 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH44 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH46 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH47 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH48 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH50 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH52 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH54 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (((r + (k * w)) + w) = (r + ((k + 1) * w)))

noncomputable def multipleKnapsack_entail_wit_12_1_split_goal_7 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH42 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH44 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH46 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH47 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH48 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH50 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH52 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH54 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  ((Zlength ((replace_Znth (tail) (current) (qval_l_2)))) = (capacity_pre + 1))

noncomputable def multipleKnapsack_entail_wit_12_1_split_goal_8 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH42 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH44 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH46 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH47 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH48 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH50 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH52 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH54 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  ((Zlength ((replace_Znth (tail) (k) (qidx_l_2)))) = (capacity_pre + 1))

noncomputable def multipleKnapsack_entail_wit_12_1_split_goal_9 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH42 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH44 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH46 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH47 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH48 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH50 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH52 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH54 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  ((Zlength ((replace_Znth ((r + (k * w))) (((Znth head (replace_Znth (tail) (current) (qval_l_2)) (0 : Int)) + (k * v))) (dp_l_2)))) = (capacity_pre + 1))

noncomputable def multipleKnapsack_entail_wit_12_2 : Prop :=
  (
forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l_2 (0 : Int)) > current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH45 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH47 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH48 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "dp" ) ) (capacity_pre + 1) (replace_Znth (pos) (((Znth head (replace_Znth (tail) (current) (qval_l_2)) (0 : Int)) + (k * v))) (dp_l_2)))
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) (replace_Znth (tail) (current) (qval_l_2)))
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l_2)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l_2)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  EX qval_l : (List Int), EX qidx_l : (List Int), EX old_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ ((pos + w) = (r + ((k + 1) * w))) ” &&
  “ ((0 : Int) <= (k + 1)) ” &&
  “ ((k + 1) <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= (pos + w)) ” &&
  “ ((pos + w) <= (capacity_pre + w)) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= (tail + 1)) ” &&
  “ ((tail + 1) <= (k + 1)) ” &&
  “ ((tail + 1) <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) old_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000000)) old_l) ” &&
  “ forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000))) ” &&
  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt (k + 1) capacity_pre) ” &&
  “ (MKQueueResultSemantics old_l qidx_l qval_l head (tail + 1) r w v cnt (k + 1) capacity_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((-(((k + 1) - 1) * v)))) (sublist (head) ((tail + 1)) (qval_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) ((1000000 - (((k + 1) - 1) * v)))) (sublist (head) ((tail + 1)) (qval_l))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l_2 (0 : Int)) > current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH45 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH47 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH48 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  TT && emp 
|--
  “ (Forall ((GE.ge (α := Int)) ((1000000 - (((k + 1) - 1) * v)))) (sublist (head) ((tail + 1)) ((replace_Znth (tail) (current) (qval_l_2))))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-(((k + 1) - 1) * v)))) (sublist (head) ((tail + 1)) ((replace_Znth (tail) (current) (qval_l_2))))) ” &&
  “ (MKQueueResultSemantics old_l_2 (replace_Znth (tail) (k) (qidx_l_2)) (replace_Znth (tail) (current) (qval_l_2)) head (tail + 1) r w v cnt (k + 1) capacity_pre) ” &&
  “ (MKItemResiduePrefixSemantics old_l_2 (replace_Znth ((r + (k * w))) (((Znth head (replace_Znth (tail) (current) (qval_l_2)) (0 : Int)) + (k * v))) (dp_l_2)) r w v cnt (k + 1) capacity_pre) ” &&
  “ forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000))) ” &&
  “ (((r + (k * w)) + w) = (r + ((k + 1) * w))) ” &&
  “ ((Zlength ((replace_Znth (tail) (current) (qval_l_2)))) = (capacity_pre + 1)) ” &&
  “ ((Zlength ((replace_Znth (tail) (k) (qidx_l_2)))) = (capacity_pre + 1)) ” &&
  “ ((Zlength ((replace_Znth ((r + (k * w))) (((Znth head (replace_Znth (tail) (current) (qval_l_2)) (0 : Int)) + (k * v))) (dp_l_2)))) = (capacity_pre + 1)) ”
  &&  emp
)

noncomputable def multipleKnapsack_entail_wit_12_2_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l_2 (0 : Int)) > current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH45 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH47 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH48 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (Forall ((GE.ge (α := Int)) ((1000000 - (((k + 1) - 1) * v)))) (sublist (head) ((tail + 1)) ((replace_Znth (tail) (current) (qval_l_2)))))

noncomputable def multipleKnapsack_entail_wit_12_2_split_goal_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l_2 (0 : Int)) > current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH45 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH47 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH48 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (Forall ((LE.le (α := Int)) ((-(((k + 1) - 1) * v)))) (sublist (head) ((tail + 1)) ((replace_Znth (tail) (current) (qval_l_2)))))

noncomputable def multipleKnapsack_entail_wit_12_2_split_goal_3 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l_2 (0 : Int)) > current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH45 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH47 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH48 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (MKQueueResultSemantics old_l_2 (replace_Znth (tail) (k) (qidx_l_2)) (replace_Znth (tail) (current) (qval_l_2)) head (tail + 1) r w v cnt (k + 1) capacity_pre)

noncomputable def multipleKnapsack_entail_wit_12_2_split_goal_4 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l_2 (0 : Int)) > current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH45 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH47 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH48 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (MKItemResiduePrefixSemantics old_l_2 (replace_Znth ((r + (k * w))) (((Znth head (replace_Znth (tail) (current) (qval_l_2)) (0 : Int)) + (k * v))) (dp_l_2)) r w v cnt (k + 1) capacity_pre)

noncomputable def multipleKnapsack_entail_wit_12_2_split_goal_5 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l_2 (0 : Int)) > current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH45 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH47 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH48 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))

noncomputable def multipleKnapsack_entail_wit_12_2_split_goal_6 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l_2 (0 : Int)) > current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH45 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH47 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH48 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (((r + (k * w)) + w) = (r + ((k + 1) * w)))

noncomputable def multipleKnapsack_entail_wit_12_2_split_goal_7 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l_2 (0 : Int)) > current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH45 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH47 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH48 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  ((Zlength ((replace_Znth (tail) (current) (qval_l_2)))) = (capacity_pre + 1))

noncomputable def multipleKnapsack_entail_wit_12_2_split_goal_8 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l_2 (0 : Int)) > current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH45 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH47 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH48 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  ((Zlength ((replace_Znth (tail) (k) (qidx_l_2)))) = (capacity_pre + 1))

noncomputable def multipleKnapsack_entail_wit_12_2_split_goal_9 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l_2 (0 : Int)) > current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH45 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH47 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current)) (PreH48 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  ((Zlength ((replace_Znth ((r + (k * w))) (((Znth head (replace_Znth (tail) (current) (qval_l_2)) (0 : Int)) + (k * v))) (dp_l_2)))) = (capacity_pre + 1))

noncomputable def multipleKnapsack_entail_wit_13 : Prop :=
  (
forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (pos > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH38 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH39 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH41 : (MKQueueResultSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre)) (PreH42 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH43 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH44 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH45 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH46 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH48 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH49 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l_2)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l_2)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l_2)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l_2)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  EX qval_l : (List Int), EX qidx_l : (List Int), EX old_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ ((0 : Int) <= (r + 1)) ” &&
  “ ((r + 1) <= w) ” &&
  “ ((r + 1) <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) old_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000000)) old_l) ” &&
  “ forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000))) ” &&
  “ (MKItemResidueProgressSemantics old_l dp_l (r + 1) w v cnt capacity_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (pos > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH38 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH39 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH41 : (MKQueueResultSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre)) (PreH42 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH43 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH44 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH45 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH46 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH48 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH49 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  TT && emp 
|--
  “ (MKItemResidueProgressSemantics old_l_2 dp_l_2 (r + 1) w v cnt capacity_pre) ” &&
  “ forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000))) ”
  &&  emp
)

noncomputable def multipleKnapsack_entail_wit_13_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (pos > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH38 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH39 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH41 : (MKQueueResultSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre)) (PreH42 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH43 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH44 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH45 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH46 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH48 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH49 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (MKItemResidueProgressSemantics old_l_2 dp_l_2 (r + 1) w v cnt capacity_pre)

noncomputable def multipleKnapsack_entail_wit_13_split_goal_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (pos > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH38 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH39 : forall (p_2 : Int) , forall (a_2 : Int) , (((((0 : Int) <= p_2) ∧ (p_2 <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2)) -> (((0 : Int) <= a_2) ∧ (a_2 <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre)) (PreH41 : (MKQueueResultSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre)) (PreH42 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH43 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l_2)))) (PreH44 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH45 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH46 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH48 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH49 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))

noncomputable def multipleKnapsack_entail_wit_14 : Prop :=
  (
forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (r : Int) (cnt : Int) (v : Int) (w : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (r >= w)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : (w = (Znth i weights_l (0 : Int)))) (PreH16 : (v = (Znth i values_l (0 : Int)))) (PreH17 : (cnt = (Znth i counts_l (0 : Int)))) (PreH18 : (1 <= w)) (PreH19 : (w <= (capacity_pre + 1))) (PreH20 : ((0 : Int) <= v)) (PreH21 : (v <= 1000)) (PreH22 : ((0 : Int) <= cnt)) (PreH23 : (cnt <= capacity_pre)) (PreH24 : ((0 : Int) <= r)) (PreH25 : (r <= w)) (PreH26 : (r <= (capacity_pre + 1))) (PreH27 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH28 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH29 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH30 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH31 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 r w v cnt capacity_pre)) (PreH32 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH33 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH34 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH35 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH36 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH37 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l_2)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l_2)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l_2)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l_2)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  EX qval_l : (List Int), EX qidx_l : (List Int), EX old_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l (i + 1) capacity_pre dp_l) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (r : Int) (cnt : Int) (v : Int) (w : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (r >= w)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : (w = (Znth i weights_l (0 : Int)))) (PreH16 : (v = (Znth i values_l (0 : Int)))) (PreH17 : (cnt = (Znth i counts_l (0 : Int)))) (PreH18 : (1 <= w)) (PreH19 : (w <= (capacity_pre + 1))) (PreH20 : ((0 : Int) <= v)) (PreH21 : (v <= 1000)) (PreH22 : ((0 : Int) <= cnt)) (PreH23 : (cnt <= capacity_pre)) (PreH24 : ((0 : Int) <= r)) (PreH25 : (r <= w)) (PreH26 : (r <= (capacity_pre + 1))) (PreH27 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH28 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH29 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH30 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH31 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 r w v cnt capacity_pre)) (PreH32 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH33 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH34 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH35 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH36 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH37 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  TT && emp 
|--
  “ (MKDPTableSemantics weights_l values_l counts_l (i + 1) capacity_pre dp_l_2) ”
  &&  emp
)

noncomputable def multipleKnapsack_entail_wit_14_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (r : Int) (cnt : Int) (v : Int) (w : Int) (i : Int) (qval_l_2 : (List Int)) (qidx_l_2 : (List Int)) (old_l_2 : (List Int)) (dp_l_2 : (List Int)) (PreH1 : (r >= w)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : (w = (Znth i weights_l (0 : Int)))) (PreH16 : (v = (Znth i values_l (0 : Int)))) (PreH17 : (cnt = (Znth i counts_l (0 : Int)))) (PreH18 : (1 <= w)) (PreH19 : (w <= (capacity_pre + 1))) (PreH20 : ((0 : Int) <= v)) (PreH21 : (v <= 1000)) (PreH22 : ((0 : Int) <= cnt)) (PreH23 : (cnt <= capacity_pre)) (PreH24 : ((0 : Int) <= r)) (PreH25 : (r <= w)) (PreH26 : (r <= (capacity_pre + 1))) (PreH27 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2)) (PreH28 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l_2)) (PreH29 : (Forall ((GE.ge (α := Int)) (1000000)) old_l_2)) (PreH30 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH31 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 r w v cnt capacity_pre)) (PreH32 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH33 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH34 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH35 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH36 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH37 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (MKDPTableSemantics weights_l values_l counts_l (i + 1) capacity_pre dp_l_2)

noncomputable def multipleKnapsack_entail_wit_15 : Prop :=
  (
forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l)) (PreH16 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH17 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ (MultipleKnapsackAnswer weights_l values_l counts_l capacity_pre (Znth capacity_pre dp_l (0 : Int))) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.undef_full ( &( "dp" ) ) 1001)
  ** (intArray.undef_full ( &( "old" ) ) 1001)
  ** (intArray.undef_full ( &( "q_idx" ) ) 1001)
  ** (intArray.undef_full ( &( "q_val" ) ) 1001)
) \/
(
forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l)) (PreH16 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH17 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ (MultipleKnapsackAnswer weights_l values_l counts_l capacity_pre (Znth capacity_pre dp_l (0 : Int))) ”
  &&  (intArray.undef_full ( &( "dp" ) ) 1001)
  ** (intArray.undef_full ( &( "old" ) ) 1001)
  ** (intArray.undef_full ( &( "q_idx" ) ) 1001)
  ** (intArray.undef_full ( &( "q_val" ) ) 1001)
)

noncomputable def multipleKnapsack_entail_wit_15_split_goal_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l)) (PreH16 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH17 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ (MultipleKnapsackAnswer weights_l values_l counts_l capacity_pre (Znth capacity_pre dp_l (0 : Int))) ”

noncomputable def multipleKnapsack_entail_wit_15_split_goal_spatial : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l)) (PreH16 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH17 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  (intArray.undef_full ( &( "dp" ) ) 1001)
  ** (intArray.undef_full ( &( "old" ) ) 1001)
  ** (intArray.undef_full ( &( "q_idx" ) ) 1001)
  ** (intArray.undef_full ( &( "q_val" ) ) 1001)

noncomputable def multipleKnapsack_return_wit_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (answer : Int) (PreH1 : (MultipleKnapsackAnswer weights_l values_l counts_l capacity_pre answer)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
|--
  “ (MultipleKnapsackAnswer weights_l values_l counts_l capacity_pre answer) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)

noncomputable def multipleKnapsack_partial_solve_wit_1 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (qval0 : (List Int)) (qidx0 : (List Int)) (old0 : (List Int)) (j : Int) (dp_l : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = j)) (PreH10 : ((Zlength (old0)) = j)) (PreH11 : ((Zlength (qidx0)) = j)) (PreH12 : ((Zlength (qval0)) = j)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= (capacity_pre + 1))) (PreH15 : (Forall (Eq ((0 : Int))) dp_l)) (PreH16 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH17 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) j dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) j 1001)
  ** (intArray.seg ( &( "old" ) ) (0 : Int) j old0)
  ** (intArray.undef_seg ( &( "old" ) ) j 1001)
  ** (intArray.seg ( &( "q_idx" ) ) (0 : Int) j qidx0)
  ** (intArray.undef_seg ( &( "q_idx" ) ) j 1001)
  ** (intArray.seg ( &( "q_val" ) ) (0 : Int) j qval0)
  ** (intArray.undef_seg ( &( "q_val" ) ) j 1001)
|--
  “ (j <= capacity_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = j) ” &&
  “ ((Zlength (old0)) = j) ” &&
  “ ((Zlength (qidx0)) = j) ” &&
  “ ((Zlength (qval0)) = j) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (capacity_pre + 1)) ” &&
  “ (Forall (Eq ((0 : Int))) dp_l) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (((( &( "dp" ) ) + (j * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg ( &( "dp" ) ) (j + 1) 1001)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) j dp_l)
  ** (intArray.seg ( &( "old" ) ) (0 : Int) j old0)
  ** (intArray.undef_seg ( &( "old" ) ) j 1001)
  ** (intArray.seg ( &( "q_idx" ) ) (0 : Int) j qidx0)
  ** (intArray.undef_seg ( &( "q_idx" ) ) j 1001)
  ** (intArray.seg ( &( "q_val" ) ) (0 : Int) j qval0)
  ** (intArray.undef_seg ( &( "q_val" ) ) j 1001)

noncomputable def multipleKnapsack_partial_solve_wit_2 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (qval0 : (List Int)) (qidx0 : (List Int)) (old0 : (List Int)) (j : Int) (dp_l : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = j)) (PreH10 : ((Zlength (old0)) = j)) (PreH11 : ((Zlength (qidx0)) = j)) (PreH12 : ((Zlength (qval0)) = j)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= (capacity_pre + 1))) (PreH15 : (Forall (Eq ((0 : Int))) dp_l)) (PreH16 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH17 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.seg ( &( "dp" ) ) (0 : Int) (j + 1) (dp_l ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "dp" ) ) (j + 1) 1001)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.seg ( &( "old" ) ) (0 : Int) j old0)
  ** (intArray.undef_seg ( &( "old" ) ) j 1001)
  ** (intArray.seg ( &( "q_idx" ) ) (0 : Int) j qidx0)
  ** (intArray.undef_seg ( &( "q_idx" ) ) j 1001)
  ** (intArray.seg ( &( "q_val" ) ) (0 : Int) j qval0)
  ** (intArray.undef_seg ( &( "q_val" ) ) j 1001)
|--
  “ (j <= capacity_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = j) ” &&
  “ ((Zlength (old0)) = j) ” &&
  “ ((Zlength (qidx0)) = j) ” &&
  “ ((Zlength (qval0)) = j) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (capacity_pre + 1)) ” &&
  “ (Forall (Eq ((0 : Int))) dp_l) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (((( &( "old" ) ) + (j * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg ( &( "old" ) ) (j + 1) 1001)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) (j + 1) (dp_l ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "dp" ) ) (j + 1) 1001)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.seg ( &( "old" ) ) (0 : Int) j old0)
  ** (intArray.seg ( &( "q_idx" ) ) (0 : Int) j qidx0)
  ** (intArray.undef_seg ( &( "q_idx" ) ) j 1001)
  ** (intArray.seg ( &( "q_val" ) ) (0 : Int) j qval0)
  ** (intArray.undef_seg ( &( "q_val" ) ) j 1001)

noncomputable def multipleKnapsack_partial_solve_wit_3 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (qval0 : (List Int)) (qidx0 : (List Int)) (old0 : (List Int)) (j : Int) (dp_l : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = j)) (PreH10 : ((Zlength (old0)) = j)) (PreH11 : ((Zlength (qidx0)) = j)) (PreH12 : ((Zlength (qval0)) = j)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= (capacity_pre + 1))) (PreH15 : (Forall (Eq ((0 : Int))) dp_l)) (PreH16 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH17 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.seg ( &( "old" ) ) (0 : Int) (j + 1) (old0 ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "old" ) ) (j + 1) 1001)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) (j + 1) (dp_l ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "dp" ) ) (j + 1) 1001)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.seg ( &( "q_idx" ) ) (0 : Int) j qidx0)
  ** (intArray.undef_seg ( &( "q_idx" ) ) j 1001)
  ** (intArray.seg ( &( "q_val" ) ) (0 : Int) j qval0)
  ** (intArray.undef_seg ( &( "q_val" ) ) j 1001)
|--
  “ (j <= capacity_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = j) ” &&
  “ ((Zlength (old0)) = j) ” &&
  “ ((Zlength (qidx0)) = j) ” &&
  “ ((Zlength (qval0)) = j) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (capacity_pre + 1)) ” &&
  “ (Forall (Eq ((0 : Int))) dp_l) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (((( &( "q_idx" ) ) + (j * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (j + 1) 1001)
  ** (intArray.seg ( &( "old" ) ) (0 : Int) (j + 1) (old0 ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "old" ) ) (j + 1) 1001)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) (j + 1) (dp_l ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "dp" ) ) (j + 1) 1001)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.seg ( &( "q_idx" ) ) (0 : Int) j qidx0)
  ** (intArray.seg ( &( "q_val" ) ) (0 : Int) j qval0)
  ** (intArray.undef_seg ( &( "q_val" ) ) j 1001)

noncomputable def multipleKnapsack_partial_solve_wit_4 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (qval0 : (List Int)) (qidx0 : (List Int)) (old0 : (List Int)) (j : Int) (dp_l : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = j)) (PreH10 : ((Zlength (old0)) = j)) (PreH11 : ((Zlength (qidx0)) = j)) (PreH12 : ((Zlength (qval0)) = j)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j <= (capacity_pre + 1))) (PreH15 : (Forall (Eq ((0 : Int))) dp_l)) (PreH16 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH17 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.seg ( &( "q_idx" ) ) (0 : Int) (j + 1) (qidx0 ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "q_idx" ) ) (j + 1) 1001)
  ** (intArray.seg ( &( "old" ) ) (0 : Int) (j + 1) (old0 ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "old" ) ) (j + 1) 1001)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) (j + 1) (dp_l ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "dp" ) ) (j + 1) 1001)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.seg ( &( "q_val" ) ) (0 : Int) j qval0)
  ** (intArray.undef_seg ( &( "q_val" ) ) j 1001)
|--
  “ (j <= capacity_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = j) ” &&
  “ ((Zlength (old0)) = j) ” &&
  “ ((Zlength (qidx0)) = j) ” &&
  “ ((Zlength (qval0)) = j) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (capacity_pre + 1)) ” &&
  “ (Forall (Eq ((0 : Int))) dp_l) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (((( &( "q_val" ) ) + (j * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg ( &( "q_val" ) ) (j + 1) 1001)
  ** (intArray.seg ( &( "q_idx" ) ) (0 : Int) (j + 1) (qidx0 ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "q_idx" ) ) (j + 1) 1001)
  ** (intArray.seg ( &( "old" ) ) (0 : Int) (j + 1) (old0 ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "old" ) ) (j + 1) 1001)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) (j + 1) (dp_l ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "dp" ) ) (j + 1) 1001)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.seg ( &( "q_val" ) ) (0 : Int) j qval0)

noncomputable def multipleKnapsack_partial_solve_wit_5 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l)) (PreH18 : (MKCopyPrefixSemantics dp_l old_l j)) (PreH19 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH20 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH22 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH23 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH24 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ (j <= capacity_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l) ” &&
  “ (MKCopyPrefixSemantics dp_l old_l j) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (((( &( "dp" ) ) + (j * sizeof(INT)))) # Int |-> ((Znth j dp_l (0 : Int))))
  ** (intArray.missing_i ( &( "dp" ) ) j (0 : Int) (capacity_pre + 1) dp_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)

noncomputable def multipleKnapsack_partial_solve_wit_6 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (j <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l)) (PreH18 : (MKCopyPrefixSemantics dp_l old_l j)) (PreH19 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH20 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH22 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH23 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH24 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ (j <= capacity_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l) ” &&
  “ (MKCopyPrefixSemantics dp_l old_l j) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (((( &( "old" ) ) + (j * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i ( &( "old" ) ) j (0 : Int) (capacity_pre + 1) old_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)

noncomputable def multipleKnapsack_partial_solve_wit_7 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (j > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l)) (PreH18 : (MKCopyPrefixSemantics dp_l old_l j)) (PreH19 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH20 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH22 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH23 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH24 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ (j > capacity_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l) ” &&
  “ (MKCopyPrefixSemantics dp_l old_l j) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (((weights_pre + (i * sizeof(INT)))) # Int |-> ((Znth i weights_l (0 : Int))))
  ** (intArray.missing_i weights_pre i (0 : Int) n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)

noncomputable def multipleKnapsack_partial_solve_wit_8 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (j > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l)) (PreH18 : (MKCopyPrefixSemantics dp_l old_l j)) (PreH19 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH20 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH22 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH23 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH24 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ (j > capacity_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l) ” &&
  “ (MKCopyPrefixSemantics dp_l old_l j) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (((values_pre + (i * sizeof(INT)))) # Int |-> ((Znth i values_l (0 : Int))))
  ** (intArray.missing_i values_pre i (0 : Int) n_pre values_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)

noncomputable def multipleKnapsack_partial_solve_wit_9 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (j : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (j > capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= (capacity_pre + 1))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l)) (PreH18 : (MKCopyPrefixSemantics dp_l old_l j)) (PreH19 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH20 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH21 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH22 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH23 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH24 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full values_pre n_pre values_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ (j > capacity_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l) ” &&
  “ (MKCopyPrefixSemantics dp_l old_l j) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (((counts_pre + (i * sizeof(INT)))) # Int |-> ((Znth i counts_l (0 : Int))))
  ** (intArray.missing_i counts_pre i (0 : Int) n_pre counts_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)

noncomputable def multipleKnapsack_partial_solve_wit_10 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (pos <= capacity_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= (capacity_pre + 1))) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= (capacity_pre + w))) (PreH32 : ((0 : Int) <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH39 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH41 : (MKQueueResultSemantics old_l qidx_l qval_l head tail r w v cnt k capacity_pre)) (PreH42 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l)))) (PreH43 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l)))) (PreH44 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH45 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH46 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH48 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH49 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ (pos <= capacity_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ (pos = (r + (k * w))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= (capacity_pre + w)) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= k) ” &&
  “ (tail <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) old_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000000)) old_l) ” &&
  “ forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000))) ” &&
  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre) ” &&
  “ (MKQueueResultSemantics old_l qidx_l qval_l head tail r w v cnt k capacity_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (((( &( "old" ) ) + (pos * sizeof(INT)))) # Int |-> ((Znth pos old_l (0 : Int))))
  ** (intArray.missing_i ( &( "old" ) ) pos (0 : Int) (capacity_pre + 1) old_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)

noncomputable def multipleKnapsack_partial_solve_wit_11 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (head < tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH42 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH44 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH46 : (MKQueueDropSemantics old_l qidx_l qval_l head tail r w v cnt k)) (PreH47 : (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l)))) (PreH48 : (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l)))) (PreH49 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH50 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH52 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH54 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ (head < tail) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ (pos = (r + (k * w))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= capacity_pre) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= capacity_pre) ” &&
  “ (current = ((Znth pos old_l (0 : Int)) - (k * v))) ” &&
  “ ((-1000000) <= current) ” &&
  “ (current <= 1000000) ” &&
  “ ((0 : Int) <= (current + (k * v))) ” &&
  “ ((current + (k * v)) <= 1000000) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= k) ” &&
  “ (tail <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) old_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000000)) old_l) ” &&
  “ forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000))) ” &&
  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre) ” &&
  “ (MKQueueDropSemantics old_l qidx_l qval_l head tail r w v cnt k) ” &&
  “ (Forall ((LE.le (α := Int)) ((-((k - 1) * v)))) (sublist (head) (tail) (qval_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) ((1000000 - ((k - 1) * v)))) (sublist (head) (tail) (qval_l))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (((( &( "q_idx" ) ) + (head * sizeof(INT)))) # Int |-> ((Znth head qidx_l (0 : Int))))
  ** (intArray.missing_i ( &( "q_idx" ) ) head (0 : Int) (capacity_pre + 1) qidx_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)

noncomputable def multipleKnapsack_partial_solve_wit_12 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (head < tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH42 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH44 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH46 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH47 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l)))) (PreH48 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l)))) (PreH49 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH50 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH52 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH54 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ (head < tail) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ (pos = (r + (k * w))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= capacity_pre) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= capacity_pre) ” &&
  “ (current = ((Znth pos old_l (0 : Int)) - (k * v))) ” &&
  “ ((-1000000) <= current) ” &&
  “ (current <= 1000000) ” &&
  “ ((0 : Int) <= (current + (k * v))) ” &&
  “ ((current + (k * v)) <= 1000000) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= k) ” &&
  “ (tail <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) old_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000000)) old_l) ” &&
  “ forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000))) ” &&
  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre) ” &&
  “ (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current) ” &&
  “ (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (((( &( "q_val" ) ) + ((tail - 1) * sizeof(INT)))) # Int |-> ((Znth (tail - 1) qval_l (0 : Int))))
  ** (intArray.missing_i ( &( "q_val" ) ) (tail - 1) (0 : Int) (capacity_pre + 1) qval_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)

noncomputable def multipleKnapsack_partial_solve_wit_13 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH42 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH44 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH46 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH47 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l)))) (PreH48 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l)))) (PreH49 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH50 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH52 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH54 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ (head >= tail) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ (pos = (r + (k * w))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= capacity_pre) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= capacity_pre) ” &&
  “ (current = ((Znth pos old_l (0 : Int)) - (k * v))) ” &&
  “ ((-1000000) <= current) ” &&
  “ (current <= 1000000) ” &&
  “ ((0 : Int) <= (current + (k * v))) ” &&
  “ ((current + (k * v)) <= 1000000) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= k) ” &&
  “ (tail <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) old_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000000)) old_l) ” &&
  “ forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000))) ” &&
  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre) ” &&
  “ (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current) ” &&
  “ (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (((( &( "q_idx" ) ) + (tail * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i ( &( "q_idx" ) ) tail (0 : Int) (capacity_pre + 1) qidx_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)

noncomputable def multipleKnapsack_partial_solve_wit_14 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l (0 : Int)) > current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH45 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH47 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH48 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ ((Znth (tail - 1) qval_l (0 : Int)) > current) ” &&
  “ (head < tail) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ (pos = (r + (k * w))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= capacity_pre) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= capacity_pre) ” &&
  “ (current = ((Znth pos old_l (0 : Int)) - (k * v))) ” &&
  “ ((-1000000) <= current) ” &&
  “ (current <= 1000000) ” &&
  “ ((0 : Int) <= (current + (k * v))) ” &&
  “ ((current + (k * v)) <= 1000000) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= k) ” &&
  “ (tail <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) old_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000000)) old_l) ” &&
  “ forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000))) ” &&
  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre) ” &&
  “ (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current) ” &&
  “ (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (((( &( "q_idx" ) ) + (tail * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i ( &( "q_idx" ) ) tail (0 : Int) (capacity_pre + 1) qidx_l)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)

noncomputable def multipleKnapsack_partial_solve_wit_15 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH42 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH44 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH46 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH47 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l)))) (PreH48 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l)))) (PreH49 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH50 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH52 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH54 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ (head >= tail) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ (pos = (r + (k * w))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= capacity_pre) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= capacity_pre) ” &&
  “ (current = ((Znth pos old_l (0 : Int)) - (k * v))) ” &&
  “ ((-1000000) <= current) ” &&
  “ (current <= 1000000) ” &&
  “ ((0 : Int) <= (current + (k * v))) ” &&
  “ ((current + (k * v)) <= 1000000) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= k) ” &&
  “ (tail <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) old_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000000)) old_l) ” &&
  “ forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000))) ” &&
  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre) ” &&
  “ (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current) ” &&
  “ (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (((( &( "q_val" ) ) + (tail * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i ( &( "q_val" ) ) tail (0 : Int) (capacity_pre + 1) qval_l)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)

noncomputable def multipleKnapsack_partial_solve_wit_16 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l (0 : Int)) > current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH45 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH47 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH48 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l)))
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ ((Znth (tail - 1) qval_l (0 : Int)) > current) ” &&
  “ (head < tail) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ (pos = (r + (k * w))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= capacity_pre) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= capacity_pre) ” &&
  “ (current = ((Znth pos old_l (0 : Int)) - (k * v))) ” &&
  “ ((-1000000) <= current) ” &&
  “ (current <= 1000000) ” &&
  “ ((0 : Int) <= (current + (k * v))) ” &&
  “ ((current + (k * v)) <= 1000000) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= k) ” &&
  “ (tail <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) old_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000000)) old_l) ” &&
  “ forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000))) ” &&
  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre) ” &&
  “ (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current) ” &&
  “ (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (((( &( "q_val" ) ) + (tail * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i ( &( "q_val" ) ) tail (0 : Int) (capacity_pre + 1) qval_l)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)

noncomputable def multipleKnapsack_partial_solve_wit_17 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH42 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH44 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH46 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH47 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l)))) (PreH48 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l)))) (PreH49 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH50 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH52 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH54 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) (replace_Znth (tail) (current) (qval_l)))
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ (head >= tail) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ (pos = (r + (k * w))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= capacity_pre) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= capacity_pre) ” &&
  “ (current = ((Znth pos old_l (0 : Int)) - (k * v))) ” &&
  “ ((-1000000) <= current) ” &&
  “ (current <= 1000000) ” &&
  “ ((0 : Int) <= (current + (k * v))) ” &&
  “ ((current + (k * v)) <= 1000000) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= k) ” &&
  “ (tail <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) old_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000000)) old_l) ” &&
  “ forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000))) ” &&
  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre) ” &&
  “ (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current) ” &&
  “ (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (((( &( "q_val" ) ) + (head * sizeof(INT)))) # Int |-> ((Znth head (replace_Znth (tail) (current) (qval_l)) (0 : Int))))
  ** (intArray.missing_i ( &( "q_val" ) ) head (0 : Int) (capacity_pre + 1) (replace_Znth (tail) (current) (qval_l)))
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)

noncomputable def multipleKnapsack_partial_solve_wit_18 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (head >= tail)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i < n_pre)) (PreH15 : ((0 : Int) <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l (0 : Int)))) (PreH19 : (v = (Znth i values_l (0 : Int)))) (PreH20 : (cnt = (Znth i counts_l (0 : Int)))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1))) (PreH23 : ((0 : Int) <= v)) (PreH24 : (v <= 1000)) (PreH25 : ((0 : Int) <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w)))) (PreH28 : ((0 : Int) <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : ((0 : Int) <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : ((0 : Int) <= (current + (k * v)))) (PreH36 : ((current + (k * v)) <= 1000000)) (PreH37 : ((0 : Int) <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH42 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH44 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH46 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH47 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l)))) (PreH48 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l)))) (PreH49 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH50 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH51 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH52 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH53 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH54 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) (replace_Znth (tail) (current) (qval_l)))
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ (head >= tail) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ (pos = (r + (k * w))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= capacity_pre) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= capacity_pre) ” &&
  “ (current = ((Znth pos old_l (0 : Int)) - (k * v))) ” &&
  “ ((-1000000) <= current) ” &&
  “ (current <= 1000000) ” &&
  “ ((0 : Int) <= (current + (k * v))) ” &&
  “ ((current + (k * v)) <= 1000000) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= k) ” &&
  “ (tail <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) old_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000000)) old_l) ” &&
  “ forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000))) ” &&
  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre) ” &&
  “ (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current) ” &&
  “ (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (((( &( "dp" ) ) + (pos * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i ( &( "dp" ) ) pos (0 : Int) (capacity_pre + 1) dp_l)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) (replace_Znth (tail) (current) (qval_l)))
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)

noncomputable def multipleKnapsack_partial_solve_wit_19 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l (0 : Int)) > current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH45 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH47 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH48 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) (replace_Znth (tail) (current) (qval_l)))
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ ((Znth (tail - 1) qval_l (0 : Int)) > current) ” &&
  “ (head < tail) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ (pos = (r + (k * w))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= capacity_pre) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= capacity_pre) ” &&
  “ (current = ((Znth pos old_l (0 : Int)) - (k * v))) ” &&
  “ ((-1000000) <= current) ” &&
  “ (current <= 1000000) ” &&
  “ ((0 : Int) <= (current + (k * v))) ” &&
  “ ((current + (k * v)) <= 1000000) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= k) ” &&
  “ (tail <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) old_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000000)) old_l) ” &&
  “ forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000))) ” &&
  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre) ” &&
  “ (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current) ” &&
  “ (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (((( &( "q_val" ) ) + (head * sizeof(INT)))) # Int |-> ((Znth head (replace_Znth (tail) (current) (qval_l)) (0 : Int))))
  ** (intArray.missing_i ( &( "q_val" ) ) head (0 : Int) (capacity_pre + 1) (replace_Znth (tail) (current) (qval_l)))
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)

noncomputable def multipleKnapsack_partial_solve_wit_20 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (tail : Int) (head : Int) (current : Int) (k : Int) (pos : Int) (cnt : Int) (v : Int) (w : Int) (r : Int) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : ((Znth (tail - 1) qval_l (0 : Int)) > current)) (PreH2 : (head < tail)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((0 : Int) <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((0 : Int) <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l (0 : Int)))) (PreH20 : (v = (Znth i values_l (0 : Int)))) (PreH21 : (cnt = (Znth i counts_l (0 : Int)))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1))) (PreH24 : ((0 : Int) <= v)) (PreH25 : (v <= 1000)) (PreH26 : ((0 : Int) <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w)))) (PreH29 : ((0 : Int) <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : ((0 : Int) <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l (0 : Int)) - (k * v)))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : ((0 : Int) <= (current + (k * v)))) (PreH37 : ((current + (k * v)) <= 1000000)) (PreH38 : ((0 : Int) <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l)) (PreH43 : (Forall ((LE.le (α := Int)) ((0 : Int))) old_l)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000000)) old_l)) (PreH45 : forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre)) (PreH47 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current)) (PreH48 : (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l)))) (PreH49 : (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l)))) (PreH50 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH51 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH52 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH53 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH54 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH55 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) (replace_Znth (tail) (current) (qval_l)))
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ ((Znth (tail - 1) qval_l (0 : Int)) > current) ” &&
  “ (head < tail) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < w) ” &&
  “ (r <= capacity_pre) ” &&
  “ (w = (Znth i weights_l (0 : Int))) ” &&
  “ (v = (Znth i values_l (0 : Int))) ” &&
  “ (cnt = (Znth i counts_l (0 : Int))) ” &&
  “ (1 <= w) ” &&
  “ (w <= (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= v) ” &&
  “ (v <= 1000) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt <= capacity_pre) ” &&
  “ (pos = (r + (k * w))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= capacity_pre) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= capacity_pre) ” &&
  “ (current = ((Znth pos old_l (0 : Int)) - (k * v))) ” &&
  “ ((-1000000) <= current) ” &&
  “ (current <= 1000000) ” &&
  “ ((0 : Int) <= (current + (k * v))) ” &&
  “ ((current + (k * v)) <= 1000000) ” &&
  “ ((0 : Int) <= head) ” &&
  “ (head <= tail) ” &&
  “ (tail <= k) ” &&
  “ (tail <= (capacity_pre + 1)) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) old_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000000)) old_l) ” &&
  “ forall (p : Int) , forall (a : Int) , (((((0 : Int) <= p) ∧ (p <= capacity_pre)) ∧ (MKTransitionSemantics old_l w v cnt capacity_pre p a)) -> (((0 : Int) <= a) ∧ (a <= 1000000))) ” &&
  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre) ” &&
  “ (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current) ” &&
  “ (Forall ((LE.le (α := Int)) ((-(k * v)))) (sublist (head) (tail) (qval_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) ((1000000 - (k * v)))) (sublist (head) (tail) (qval_l))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (((( &( "dp" ) ) + (pos * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i ( &( "dp" ) ) pos (0 : Int) (capacity_pre + 1) dp_l)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) (replace_Znth (tail) (current) (qval_l)))
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) (replace_Znth (tail) (k) (qidx_l)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)

noncomputable def multipleKnapsack_partial_solve_wit_21 : Prop :=
  forall (capacity_pre : Int) (n_pre : Int) (counts_pre : Int) (values_pre : Int) (weights_pre : Int) (counts_l : (List Int)) (values_l : (List Int)) (weights_l : (List Int)) (i : Int) (qval_l : (List Int)) (qidx_l : (List Int)) (old_l : (List Int)) (dp_l : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((0 : Int) <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1))) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l)) (PreH16 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH17 : (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l)) (PreH18 : (Forall ((LE.le (α := Int)) ((0 : Int))) values_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (1000)) values_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.full ( &( "dp" ) ) (capacity_pre + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)
|--
  “ (i >= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((0 : Int) <= capacity_pre) ” &&
  “ (capacity_pre <= 1000) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (values_l)) = n_pre) ” &&
  “ ((Zlength (counts_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (old_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qidx_l)) = (capacity_pre + 1)) ” &&
  “ ((Zlength (qval_l)) = (capacity_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((capacity_pre + 1))) weights_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) values_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) values_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) counts_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (capacity_pre)) counts_l) ”
  &&  (((( &( "dp" ) ) + (capacity_pre * sizeof(INT)))) # Int |-> ((Znth capacity_pre dp_l (0 : Int))))
  ** (intArray.missing_i ( &( "dp" ) ) capacity_pre (0 : Int) (capacity_pre + 1) dp_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full values_pre n_pre values_l)
  ** (intArray.full counts_pre n_pre counts_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "old" ) ) (capacity_pre + 1) old_l)
  ** (intArray.undef_seg ( &( "old" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_idx" ) ) (capacity_pre + 1) qidx_l)
  ** (intArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1) 1001)
  ** (intArray.full ( &( "q_val" ) ) (capacity_pre + 1) qval_l)
  ** (intArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1) 1001)


structure VC_Correct : Type where
  proof_of_multipleKnapsack_safety_wit_1 : multipleKnapsack_safety_wit_1
  proof_of_multipleKnapsack_safety_wit_2 : multipleKnapsack_safety_wit_2
  proof_of_multipleKnapsack_safety_wit_3 : multipleKnapsack_safety_wit_3
  proof_of_multipleKnapsack_safety_wit_4 : multipleKnapsack_safety_wit_4
  proof_of_multipleKnapsack_safety_wit_5 : multipleKnapsack_safety_wit_5
  proof_of_multipleKnapsack_safety_wit_6 : multipleKnapsack_safety_wit_6
  proof_of_multipleKnapsack_safety_wit_7 : multipleKnapsack_safety_wit_7
  proof_of_multipleKnapsack_safety_wit_8 : multipleKnapsack_safety_wit_8
  proof_of_multipleKnapsack_safety_wit_9 : multipleKnapsack_safety_wit_9
  proof_of_multipleKnapsack_safety_wit_10 : multipleKnapsack_safety_wit_10
  proof_of_multipleKnapsack_safety_wit_11 : multipleKnapsack_safety_wit_11
  proof_of_multipleKnapsack_safety_wit_12 : multipleKnapsack_safety_wit_12
  proof_of_multipleKnapsack_safety_wit_13 : multipleKnapsack_safety_wit_13
  proof_of_multipleKnapsack_safety_wit_14 : multipleKnapsack_safety_wit_14
  proof_of_multipleKnapsack_safety_wit_16 : multipleKnapsack_safety_wit_16
  proof_of_multipleKnapsack_safety_wit_17 : multipleKnapsack_safety_wit_17
  proof_of_multipleKnapsack_safety_wit_18 : multipleKnapsack_safety_wit_18
  proof_of_multipleKnapsack_safety_wit_19 : multipleKnapsack_safety_wit_19
  proof_of_multipleKnapsack_safety_wit_20 : multipleKnapsack_safety_wit_20
  proof_of_multipleKnapsack_safety_wit_21 : multipleKnapsack_safety_wit_21
  proof_of_multipleKnapsack_safety_wit_22 : multipleKnapsack_safety_wit_22
  proof_of_multipleKnapsack_safety_wit_23 : multipleKnapsack_safety_wit_23
  proof_of_multipleKnapsack_safety_wit_25 : multipleKnapsack_safety_wit_25
  proof_of_multipleKnapsack_safety_wit_27 : multipleKnapsack_safety_wit_27
  proof_of_multipleKnapsack_safety_wit_28 : multipleKnapsack_safety_wit_28
  proof_of_multipleKnapsack_safety_wit_29 : multipleKnapsack_safety_wit_29
  proof_of_multipleKnapsack_safety_wit_30 : multipleKnapsack_safety_wit_30
  proof_of_multipleKnapsack_safety_wit_31 : multipleKnapsack_safety_wit_31
  proof_of_multipleKnapsack_safety_wit_32 : multipleKnapsack_safety_wit_32
  proof_of_multipleKnapsack_safety_wit_33 : multipleKnapsack_safety_wit_33
  proof_of_multipleKnapsack_return_wit_1 : multipleKnapsack_return_wit_1
  proof_of_multipleKnapsack_partial_solve_wit_1 : multipleKnapsack_partial_solve_wit_1
  proof_of_multipleKnapsack_partial_solve_wit_2 : multipleKnapsack_partial_solve_wit_2
  proof_of_multipleKnapsack_partial_solve_wit_3 : multipleKnapsack_partial_solve_wit_3
  proof_of_multipleKnapsack_partial_solve_wit_4 : multipleKnapsack_partial_solve_wit_4
  proof_of_multipleKnapsack_partial_solve_wit_5 : multipleKnapsack_partial_solve_wit_5
  proof_of_multipleKnapsack_partial_solve_wit_6 : multipleKnapsack_partial_solve_wit_6
  proof_of_multipleKnapsack_partial_solve_wit_7 : multipleKnapsack_partial_solve_wit_7
  proof_of_multipleKnapsack_partial_solve_wit_8 : multipleKnapsack_partial_solve_wit_8
  proof_of_multipleKnapsack_partial_solve_wit_9 : multipleKnapsack_partial_solve_wit_9
  proof_of_multipleKnapsack_partial_solve_wit_10 : multipleKnapsack_partial_solve_wit_10
  proof_of_multipleKnapsack_partial_solve_wit_11 : multipleKnapsack_partial_solve_wit_11
  proof_of_multipleKnapsack_partial_solve_wit_12 : multipleKnapsack_partial_solve_wit_12
  proof_of_multipleKnapsack_partial_solve_wit_13 : multipleKnapsack_partial_solve_wit_13
  proof_of_multipleKnapsack_partial_solve_wit_14 : multipleKnapsack_partial_solve_wit_14
  proof_of_multipleKnapsack_partial_solve_wit_15 : multipleKnapsack_partial_solve_wit_15
  proof_of_multipleKnapsack_partial_solve_wit_16 : multipleKnapsack_partial_solve_wit_16
  proof_of_multipleKnapsack_partial_solve_wit_17 : multipleKnapsack_partial_solve_wit_17
  proof_of_multipleKnapsack_partial_solve_wit_18 : multipleKnapsack_partial_solve_wit_18
  proof_of_multipleKnapsack_partial_solve_wit_19 : multipleKnapsack_partial_solve_wit_19
  proof_of_multipleKnapsack_partial_solve_wit_20 : multipleKnapsack_partial_solve_wit_20
  proof_of_multipleKnapsack_partial_solve_wit_21 : multipleKnapsack_partial_solve_wit_21
  proof_of_multipleKnapsack_safety_wit_15 : multipleKnapsack_safety_wit_15
  proof_of_multipleKnapsack_safety_wit_24 : multipleKnapsack_safety_wit_24
  proof_of_multipleKnapsack_safety_wit_26 : multipleKnapsack_safety_wit_26
  proof_of_multipleKnapsack_entail_wit_1 : multipleKnapsack_entail_wit_1
  proof_of_multipleKnapsack_entail_wit_2 : multipleKnapsack_entail_wit_2
  proof_of_multipleKnapsack_entail_wit_3 : multipleKnapsack_entail_wit_3
  proof_of_multipleKnapsack_entail_wit_4 : multipleKnapsack_entail_wit_4
  proof_of_multipleKnapsack_entail_wit_5 : multipleKnapsack_entail_wit_5
  proof_of_multipleKnapsack_entail_wit_6 : multipleKnapsack_entail_wit_6
  proof_of_multipleKnapsack_entail_wit_7 : multipleKnapsack_entail_wit_7
  proof_of_multipleKnapsack_entail_wit_8 : multipleKnapsack_entail_wit_8
  proof_of_multipleKnapsack_entail_wit_9 : multipleKnapsack_entail_wit_9
  proof_of_multipleKnapsack_entail_wit_10_1 : multipleKnapsack_entail_wit_10_1
  proof_of_multipleKnapsack_entail_wit_10_2 : multipleKnapsack_entail_wit_10_2
  proof_of_multipleKnapsack_entail_wit_11 : multipleKnapsack_entail_wit_11
  proof_of_multipleKnapsack_entail_wit_12_1 : multipleKnapsack_entail_wit_12_1
  proof_of_multipleKnapsack_entail_wit_12_2 : multipleKnapsack_entail_wit_12_2
  proof_of_multipleKnapsack_entail_wit_13 : multipleKnapsack_entail_wit_13
  proof_of_multipleKnapsack_entail_wit_14 : multipleKnapsack_entail_wit_14
  proof_of_multipleKnapsack_entail_wit_15 : multipleKnapsack_entail_wit_15

end SimpleC.EE.LLM_bench.Algorithms.multiple_knapsack.multiple_knapsack_goal
