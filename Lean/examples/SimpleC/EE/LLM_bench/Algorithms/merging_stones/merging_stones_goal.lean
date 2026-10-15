import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.merging_stones.merging_stones_lib
open SimpleC.EE.LLM_bench.Algorithms.merging_stones.merging_stones_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.merging_stones.merging_stones_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance merging_stones_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def mergingStones_safety_wit_1 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (stones_l)) = n_pre)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) ,
  ((( &( "k" ) )) # Int |->_)
  ** (intArray.undef_full ( &( "dp" ) ) 64)
  ** (intArray.undef_full ( &( "prefix" ) ) 9)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full stones_pre n_pre stones_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def mergingStones_safety_wit_2 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_flat : (List Int)) (k : Int) (PreH1 : ((0 : Int) <= k)) (PreH2 : (k <= (n_pre * n_pre))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (stones_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) ,
  ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.undef_full ( &( "prefix" ) ) 9)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) k dp_flat)
  ** (intArray.undef_seg ( &( "dp" ) ) k 64)
|--
  “ ((n_pre * n_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre * n_pre)) ”

noncomputable def mergingStones_safety_wit_3 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_flat : (List Int)) (k : Int) (PreH1 : (k < (n_pre * n_pre))) (PreH2 : ((0 : Int) <= k)) (PreH3 : (k <= (n_pre * n_pre))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH8 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) ,
  ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.undef_full ( &( "prefix" ) ) 9)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) k dp_flat)
  ** (intArray.undef_seg ( &( "dp" ) ) k 64)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def mergingStones_safety_wit_4 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_flat : (List Int)) (k : Int) (PreH1 : (k < (n_pre * n_pre))) (PreH2 : ((0 : Int) <= k)) (PreH3 : (k <= (n_pre * n_pre))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH8 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) ,
  (intArray.seg ( &( "dp" ) ) (0 : Int) (k + 1) (dp_flat ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "dp" ) ) (k + 1) 64)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.undef_full ( &( "prefix" ) ) 9)
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def mergingStones_safety_wit_5 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_flat : (List Int)) (k : Int) (PreH1 : (k >= (n_pre * n_pre))) (PreH2 : ((0 : Int) <= k)) (PreH3 : (k <= (n_pre * n_pre))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH8 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) ,
  ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.undef_full ( &( "prefix" ) ) 9)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) k dp_flat)
  ** (intArray.undef_seg ( &( "dp" ) ) k 64)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def mergingStones_safety_wit_6 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_flat : (List Int)) (k : Int) (PreH1 : (k >= (n_pre * n_pre))) (PreH2 : ((0 : Int) <= k)) (PreH3 : (k <= (n_pre * n_pre))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH8 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) ,
  ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.undef_full ( &( "prefix" ) ) 9)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) k dp_flat)
  ** (intArray.undef_seg ( &( "dp" ) ) k 64)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def mergingStones_safety_wit_7 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_flat : (List Int)) (k : Int) (PreH1 : (k >= (n_pre * n_pre))) (PreH2 : ((0 : Int) <= k)) (PreH3 : (k <= (n_pre * n_pre))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH8 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) ,
  ((( &( "i" ) )) # Int |->_)
  ** (((( &( "prefix" ) ) + ((0 : Int) * sizeof(INT)))) # Int |-> ((0 : Int)))
  ** (intArray.undef_seg ( &( "prefix" ) ) 1 9)
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) k dp_flat)
  ** (intArray.undef_seg ( &( "dp" ) ) k 64)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def mergingStones_safety_wit_8 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (i : Int) (dp_init : (List (List Int))) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_init)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l i)) ,
  ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.seg ( &( "prefix" ) ) (0 : Int) (i + 1) prefix_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (i + 1) (n_pre + 1))
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_init)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def mergingStones_safety_wit_9 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (i : Int) (dp_init : (List (List Int))) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_init)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l i)) ,
  ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.seg ( &( "prefix" ) ) (0 : Int) (i + 1) prefix_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (i + 1) (n_pre + 1))
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_init)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def mergingStones_safety_wit_10 : Prop :=
  (
forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (i : Int) (dp_init : (List (List Int))) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_init)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l i)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.seg ( &( "prefix" ) ) (0 : Int) (i + 1) prefix_l)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_seg ( &( "prefix" ) ) (i + 1) (n_pre + 1))
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_init)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ (((Znth (i - (0 : Int)) prefix_l (0 : Int)) + (Znth i stones_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth (i - (0 : Int)) prefix_l (0 : Int)) + (Znth i stones_l (0 : Int)))) ”
) \/
(
forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (i : Int) (dp_init : (List (List Int))) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_init)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l i)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.seg ( &( "prefix" ) ) (0 : Int) (i + 1) prefix_l)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_seg ( &( "prefix" ) ) (i + 1) (n_pre + 1))
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_init)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ (((Znth (i - (0 : Int)) prefix_l (0 : Int)) + (Znth i stones_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth (i - (0 : Int)) prefix_l (0 : Int)) + (Znth i stones_l (0 : Int)))) ”
)

noncomputable def mergingStones_safety_wit_10_split_goal_1 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (i : Int) (dp_init : (List (List Int))) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_init)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l i)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.seg ( &( "prefix" ) ) (0 : Int) (i + 1) prefix_l)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_seg ( &( "prefix" ) ) (i + 1) (n_pre + 1))
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_init)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ (((Znth (i - (0 : Int)) prefix_l (0 : Int)) + (Znth i stones_l (0 : Int))) <= INT_MAX) ”

noncomputable def mergingStones_safety_wit_10_split_goal_2 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (i : Int) (dp_init : (List (List Int))) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_init)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l i)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.seg ( &( "prefix" ) ) (0 : Int) (i + 1) prefix_l)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_seg ( &( "prefix" ) ) (i + 1) (n_pre + 1))
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_init)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ ((INT_MIN) <= ((Znth (i - (0 : Int)) prefix_l (0 : Int)) + (Znth i stones_l (0 : Int)))) ”

noncomputable def mergingStones_safety_wit_11 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (i : Int) (dp_init : (List (List Int))) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_init)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l i)) ,
  (intArray.seg ( &( "prefix" ) ) (0 : Int) ((i + 1) + 1) (prefix_l ++ (((Znth (i - (0 : Int)) prefix_l (0 : Int)) + (Znth i stones_l (0 : Int))) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "prefix" ) ) ((i + 1) + 1) (n_pre + 1))
  ** (intArray.full stones_pre n_pre stones_l)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_init)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def mergingStones_safety_wit_12 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (i : Int) (dp_init : (List (List Int))) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_init)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l i)) ,
  ((( &( "row" ) )) # Int |->_)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.seg ( &( "prefix" ) ) (0 : Int) (i + 1) prefix_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (i + 1) (n_pre + 1))
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_init)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def mergingStones_safety_wit_13 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (row : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (PreH1 : (row < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : ((0 : Int) <= row)) (PreH9 : (row <= n_pre)) (PreH10 : (StoneZeroRows dp_l row)) ,
  ((( &( "col" ) )) # Int |->_)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "row" ) )) # Int |-> (row))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def mergingStones_safety_wit_14 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (col : Int) (row : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (PreH1 : (col < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : ((0 : Int) <= row)) (PreH9 : (row < n_pre)) (PreH10 : ((0 : Int) <= col)) (PreH11 : (col <= n_pre)) (PreH12 : (StoneZeroProgress dp_l row col)) ,
  ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "row" ) )) # Int |-> (row))
  ** ((( &( "col" ) )) # Int |-> (col))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ ((row * n_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (row * n_pre)) ”

noncomputable def mergingStones_safety_wit_15 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (col : Int) (row : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (PreH1 : (col < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : ((0 : Int) <= row)) (PreH9 : (row < n_pre)) (PreH10 : ((0 : Int) <= col)) (PreH11 : (col <= n_pre)) (PreH12 : (StoneZeroProgress dp_l row col)) ,
  ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "row" ) )) # Int |-> (row))
  ** ((( &( "col" ) )) # Int |-> (col))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def mergingStones_safety_wit_16 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (col : Int) (row : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (PreH1 : (col < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : ((0 : Int) <= row)) (PreH9 : (row < n_pre)) (PreH10 : ((0 : Int) <= col)) (PreH11 : (col <= n_pre)) (PreH12 : (StoneZeroProgress dp_l row col)) ,
  ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "row" ) )) # Int |-> (row))
  ** ((( &( "col" ) )) # Int |-> (col))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def mergingStones_safety_wit_17 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (col : Int) (row : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (col < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : ((0 : Int) <= row)) (PreH9 : (row < n_pre)) (PreH10 : ((0 : Int) <= col)) (PreH11 : (col <= n_pre)) (PreH12 : (StoneZeroProgress dp_l row col)) ,
  (((( &( "dp" ) ) + (((row * n_pre) + col) * sizeof(INT)))) # Int |-> ((0 : Int)))
  ** (intArray.missing_i (( &( "dp" ) ) + ((row * n_pre) * sizeof(INT))) col (0 : Int) n_pre (Znth row dp_l __default__List_Z))
  ** (intArray2.missing_i ( &( "dp" ) ) row (0 : Int) n_pre n_pre dp_l)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "row" ) )) # Int |-> (row))
  ** ((( &( "col" ) )) # Int |-> (col))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ ((col + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (col + 1)) ”

noncomputable def mergingStones_safety_wit_18 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (col : Int) (row : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (PreH1 : (col >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : ((0 : Int) <= row)) (PreH9 : (row < n_pre)) (PreH10 : ((0 : Int) <= col)) (PreH11 : (col <= n_pre)) (PreH12 : (StoneZeroProgress dp_l row col)) ,
  ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "row" ) )) # Int |-> (row))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ ((row + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (row + 1)) ”

noncomputable def mergingStones_safety_wit_19 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (row : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (PreH1 : (row >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : ((0 : Int) <= row)) (PreH9 : (row <= n_pre)) (PreH10 : (StoneZeroRows dp_l row)) ,
  ((( &( "len" ) )) # Int |->_)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def mergingStones_safety_wit_20 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (len : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (PreH1 : (len <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1))) (PreH10 : (StoneLenDone stones_l dp_l n_pre len)) ,
  ((( &( "left" ) )) # Int |->_)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def mergingStones_safety_wit_21 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (left : Int) (len : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH5 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH6 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left <= ((n_pre - len) + 1))) (PreH11 : (StoneLeftProgress stones_l dp_l n_pre len left)) ,
  ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ ((left + len) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left + len)) ”

noncomputable def mergingStones_safety_wit_22 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (left : Int) (len : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (PreH1 : ((left + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= ((n_pre - len) + 1))) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left)) ,
  ((( &( "right" ) )) # Int |->_)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ (((left + len) - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((left + len) - 1)) ”

noncomputable def mergingStones_safety_wit_23 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (left : Int) (len : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (PreH1 : ((left + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= ((n_pre - len) + 1))) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left)) ,
  ((( &( "right" ) )) # Int |->_)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ ((left + len) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left + len)) ”

noncomputable def mergingStones_safety_wit_24 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (left : Int) (len : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (PreH1 : ((left + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= ((n_pre - len) + 1))) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left)) ,
  ((( &( "right" ) )) # Int |->_)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def mergingStones_safety_wit_25 : Prop :=
  (
forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (left : Int) (len : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (PreH1 : ((left + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= ((n_pre - len) + 1))) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left)) ,
  (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** ((( &( "interval_sum" ) )) # Int |->_)
  ** ((( &( "right" ) )) # Int |-> (((left + len) - 1)))
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ (((Znth (((left + len) - 1) + 1) prefix_l (0 : Int)) - (Znth left prefix_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth (((left + len) - 1) + 1) prefix_l (0 : Int)) - (Znth left prefix_l (0 : Int)))) ”
) \/
(
forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (left : Int) (len : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (PreH1 : ((left + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= ((n_pre - len) + 1))) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left)) ,
  (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** ((( &( "interval_sum" ) )) # Int |->_)
  ** ((( &( "right" ) )) # Int |-> (((left + len) - 1)))
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ (((Znth (((left + len) - 1) + 1) prefix_l (0 : Int)) - (Znth left prefix_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth (((left + len) - 1) + 1) prefix_l (0 : Int)) - (Znth left prefix_l (0 : Int)))) ”
)

noncomputable def mergingStones_safety_wit_25_split_goal_1 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (left : Int) (len : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (PreH1 : ((left + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= ((n_pre - len) + 1))) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left)) ,
  (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** ((( &( "interval_sum" ) )) # Int |->_)
  ** ((( &( "right" ) )) # Int |-> (((left + len) - 1)))
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ (((Znth (((left + len) - 1) + 1) prefix_l (0 : Int)) - (Znth left prefix_l (0 : Int))) <= INT_MAX) ”

noncomputable def mergingStones_safety_wit_25_split_goal_2 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (left : Int) (len : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (PreH1 : ((left + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= ((n_pre - len) + 1))) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left)) ,
  (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** ((( &( "interval_sum" ) )) # Int |->_)
  ** ((( &( "right" ) )) # Int |-> (((left + len) - 1)))
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ ((INT_MIN) <= ((Znth (((left + len) - 1) + 1) prefix_l (0 : Int)) - (Znth left prefix_l (0 : Int)))) ”

noncomputable def mergingStones_safety_wit_26 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (left : Int) (len : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (PreH1 : ((left + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= ((n_pre - len) + 1))) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left)) ,
  ((( &( "interval_sum" ) )) # Int |->_)
  ** ((( &( "right" ) )) # Int |-> (((left + len) - 1)))
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ ((((left + len) - 1) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((left + len) - 1) + 1)) ”

noncomputable def mergingStones_safety_wit_27 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (left : Int) (len : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (PreH1 : ((left + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= ((n_pre - len) + 1))) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left)) ,
  ((( &( "interval_sum" ) )) # Int |->_)
  ** ((( &( "right" ) )) # Int |-> (((left + len) - 1)))
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def mergingStones_safety_wit_28 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (left : Int) (len : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (PreH1 : ((left + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= ((n_pre - len) + 1))) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left)) ,
  ((( &( "best" ) )) # Int |->_)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** ((( &( "interval_sum" ) )) # Int |-> (((Znth (((left + len) - 1) + 1) prefix_l (0 : Int)) - (Znth left prefix_l (0 : Int)))))
  ** ((( &( "right" ) )) # Int |-> (((left + len) - 1)))
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ (1000000 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1000000) ”

noncomputable def mergingStones_safety_wit_29 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (best : Int) (interval_sum : Int) (split : Int) (right : Int) (left : Int) (len : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (PreH1 : (split < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : ((left + len) <= n_pre)) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left <= split)) (PreH14 : (split <= right)) (PreH15 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH16 : (2 <= interval_sum)) (PreH17 : (interval_sum <= 8000)) (PreH18 : ((0 : Int) <= best)) (PreH19 : (best <= 1000000)) (PreH20 : (StoneSplitProgress stones_l dp_l n_pre len left split best)) ,
  ((( &( "left_value" ) )) # Int |->_)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "interval_sum" ) )) # Int |-> (interval_sum))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ ((left * n_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left * n_pre)) ”

noncomputable def mergingStones_safety_wit_30 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (best : Int) (interval_sum : Int) (split : Int) (right : Int) (left : Int) (len : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (PreH1 : (split < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : ((left + len) <= n_pre)) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left <= split)) (PreH14 : (split <= right)) (PreH15 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH16 : (2 <= interval_sum)) (PreH17 : (interval_sum <= 8000)) (PreH18 : ((0 : Int) <= best)) (PreH19 : (best <= 1000000)) (PreH20 : (StoneSplitProgress stones_l dp_l n_pre len left split best)) ,
  ((( &( "left_value" ) )) # Int |->_)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "interval_sum" ) )) # Int |-> (interval_sum))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def mergingStones_safety_wit_31 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (dp_l : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (interval_sum : Int) (best : Int) (left_value : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH5 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH6 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : ((left + len) <= n_pre)) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split <= right)) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH15 : (2 <= interval_sum)) (PreH16 : (interval_sum <= 8000)) (PreH17 : ((0 : Int) <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitProgress stones_l dp_l n_pre len left split best)) (PreH20 : (split < right)) (PreH21 : (left_value = (Znth split (Znth left dp_l __default__List_Z) (0 : Int)))) ,
  ((( &( "right_value" ) )) # Int |->_)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "interval_sum" ) )) # Int |-> (interval_sum))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ (((split + 1) * n_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((split + 1) * n_pre)) ”

noncomputable def mergingStones_safety_wit_32 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (dp_l : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (interval_sum : Int) (best : Int) (left_value : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH5 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH6 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : ((left + len) <= n_pre)) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split <= right)) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH15 : (2 <= interval_sum)) (PreH16 : (interval_sum <= 8000)) (PreH17 : ((0 : Int) <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitProgress stones_l dp_l n_pre len left split best)) (PreH20 : (split < right)) (PreH21 : (left_value = (Znth split (Znth left dp_l __default__List_Z) (0 : Int)))) ,
  ((( &( "right_value" ) )) # Int |->_)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "interval_sum" ) )) # Int |-> (interval_sum))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ ((split + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (split + 1)) ”

noncomputable def mergingStones_safety_wit_33 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (dp_l : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (interval_sum : Int) (best : Int) (left_value : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH5 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH6 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : ((left + len) <= n_pre)) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split <= right)) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH15 : (2 <= interval_sum)) (PreH16 : (interval_sum <= 8000)) (PreH17 : ((0 : Int) <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitProgress stones_l dp_l n_pre len left split best)) (PreH20 : (split < right)) (PreH21 : (left_value = (Znth split (Znth left dp_l __default__List_Z) (0 : Int)))) ,
  ((( &( "right_value" ) )) # Int |->_)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "interval_sum" ) )) # Int |-> (interval_sum))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def mergingStones_safety_wit_34 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (dp_l : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (interval_sum : Int) (best : Int) (left_value : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH5 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH6 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : ((left + len) <= n_pre)) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split <= right)) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH15 : (2 <= interval_sum)) (PreH16 : (interval_sum <= 8000)) (PreH17 : ((0 : Int) <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitProgress stones_l dp_l n_pre len left split best)) (PreH20 : (split < right)) (PreH21 : (left_value = (Znth split (Znth left dp_l __default__List_Z) (0 : Int)))) ,
  ((( &( "right_value" ) )) # Int |->_)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "interval_sum" ) )) # Int |-> (interval_sum))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def mergingStones_safety_wit_35 : Prop :=
  (
forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (dp_l : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (interval_sum : Int) (best : Int) (left_value : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH5 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH6 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : ((left + len) <= n_pre)) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split <= right)) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH15 : (2 <= interval_sum)) (PreH16 : (interval_sum <= 8000)) (PreH17 : ((0 : Int) <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitProgress stones_l dp_l n_pre len left split best)) (PreH20 : (split < right)) (PreH21 : (left_value = (Znth split (Znth left dp_l __default__List_Z) (0 : Int)))) ,
  ((( &( "candidate" ) )) # Int |->_)
  ** (((( &( "dp" ) ) + ((((split + 1) * n_pre) + right) * sizeof(INT)))) # Int |-> ((Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (( &( "dp" ) ) + (((split + 1) * n_pre) * sizeof(INT))) right (0 : Int) n_pre (Znth (split + 1) dp_l __default__List_Z))
  ** (intArray2.missing_i ( &( "dp" ) ) (split + 1) (0 : Int) n_pre n_pre dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))))
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "interval_sum" ) )) # Int |-> (interval_sum))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ (((left_value + (Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))) + interval_sum) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((left_value + (Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))) + interval_sum)) ”
) \/
(
forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (dp_l : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (interval_sum : Int) (best : Int) (left_value : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH5 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH6 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : ((left + len) <= n_pre)) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split <= right)) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH15 : (2 <= interval_sum)) (PreH16 : (interval_sum <= 8000)) (PreH17 : ((0 : Int) <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitProgress stones_l dp_l n_pre len left split best)) (PreH20 : (split < right)) (PreH21 : (left_value = (Znth split (Znth left dp_l __default__List_Z) (0 : Int)))) ,
  ((( &( "candidate" ) )) # Int |->_)
  ** (((( &( "dp" ) ) + ((((split + 1) * n_pre) + right) * sizeof(INT)))) # Int |-> ((Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (( &( "dp" ) ) + (((split + 1) * n_pre) * sizeof(INT))) right (0 : Int) n_pre (Znth (split + 1) dp_l __default__List_Z))
  ** (intArray2.missing_i ( &( "dp" ) ) (split + 1) (0 : Int) n_pre n_pre dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))))
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "interval_sum" ) )) # Int |-> (interval_sum))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ (((left_value + (Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))) + interval_sum) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((left_value + (Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))) + interval_sum)) ”
)

noncomputable def mergingStones_safety_wit_35_split_goal_1 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (dp_l : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (interval_sum : Int) (best : Int) (left_value : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH5 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH6 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : ((left + len) <= n_pre)) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split <= right)) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH15 : (2 <= interval_sum)) (PreH16 : (interval_sum <= 8000)) (PreH17 : ((0 : Int) <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitProgress stones_l dp_l n_pre len left split best)) (PreH20 : (split < right)) (PreH21 : (left_value = (Znth split (Znth left dp_l __default__List_Z) (0 : Int)))) ,
  ((( &( "candidate" ) )) # Int |->_)
  ** (((( &( "dp" ) ) + ((((split + 1) * n_pre) + right) * sizeof(INT)))) # Int |-> ((Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (( &( "dp" ) ) + (((split + 1) * n_pre) * sizeof(INT))) right (0 : Int) n_pre (Znth (split + 1) dp_l __default__List_Z))
  ** (intArray2.missing_i ( &( "dp" ) ) (split + 1) (0 : Int) n_pre n_pre dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))))
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "interval_sum" ) )) # Int |-> (interval_sum))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ (((left_value + (Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))) + interval_sum) <= INT_MAX) ”

noncomputable def mergingStones_safety_wit_35_split_goal_2 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (dp_l : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (interval_sum : Int) (best : Int) (left_value : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH5 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH6 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : ((left + len) <= n_pre)) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split <= right)) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH15 : (2 <= interval_sum)) (PreH16 : (interval_sum <= 8000)) (PreH17 : ((0 : Int) <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitProgress stones_l dp_l n_pre len left split best)) (PreH20 : (split < right)) (PreH21 : (left_value = (Znth split (Znth left dp_l __default__List_Z) (0 : Int)))) ,
  ((( &( "candidate" ) )) # Int |->_)
  ** (((( &( "dp" ) ) + ((((split + 1) * n_pre) + right) * sizeof(INT)))) # Int |-> ((Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (( &( "dp" ) ) + (((split + 1) * n_pre) * sizeof(INT))) right (0 : Int) n_pre (Znth (split + 1) dp_l __default__List_Z))
  ** (intArray2.missing_i ( &( "dp" ) ) (split + 1) (0 : Int) n_pre n_pre dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))))
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "interval_sum" ) )) # Int |-> (interval_sum))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ ((INT_MIN) <= ((left_value + (Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))) + interval_sum)) ”

noncomputable def mergingStones_safety_wit_36 : Prop :=
  (
forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (dp_l : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (interval_sum : Int) (best : Int) (left_value : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH5 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH6 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : ((left + len) <= n_pre)) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split <= right)) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH15 : (2 <= interval_sum)) (PreH16 : (interval_sum <= 8000)) (PreH17 : ((0 : Int) <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitProgress stones_l dp_l n_pre len left split best)) (PreH20 : (split < right)) (PreH21 : (left_value = (Znth split (Znth left dp_l __default__List_Z) (0 : Int)))) ,
  ((( &( "candidate" ) )) # Int |->_)
  ** (((( &( "dp" ) ) + ((((split + 1) * n_pre) + right) * sizeof(INT)))) # Int |-> ((Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (( &( "dp" ) ) + (((split + 1) * n_pre) * sizeof(INT))) right (0 : Int) n_pre (Znth (split + 1) dp_l __default__List_Z))
  ** (intArray2.missing_i ( &( "dp" ) ) (split + 1) (0 : Int) n_pre n_pre dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))))
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "interval_sum" ) )) # Int |-> (interval_sum))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ ((left_value + (Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left_value + (Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int))))) ”
) \/
(
forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (dp_l : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (interval_sum : Int) (best : Int) (left_value : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH5 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH6 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : ((left + len) <= n_pre)) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split <= right)) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH15 : (2 <= interval_sum)) (PreH16 : (interval_sum <= 8000)) (PreH17 : ((0 : Int) <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitProgress stones_l dp_l n_pre len left split best)) (PreH20 : (split < right)) (PreH21 : (left_value = (Znth split (Znth left dp_l __default__List_Z) (0 : Int)))) ,
  ((( &( "candidate" ) )) # Int |->_)
  ** (((( &( "dp" ) ) + ((((split + 1) * n_pre) + right) * sizeof(INT)))) # Int |-> ((Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (( &( "dp" ) ) + (((split + 1) * n_pre) * sizeof(INT))) right (0 : Int) n_pre (Znth (split + 1) dp_l __default__List_Z))
  ** (intArray2.missing_i ( &( "dp" ) ) (split + 1) (0 : Int) n_pre n_pre dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))))
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "interval_sum" ) )) # Int |-> (interval_sum))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ ((left_value + (Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left_value + (Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int))))) ”
)

noncomputable def mergingStones_safety_wit_36_split_goal_1 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (dp_l : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (interval_sum : Int) (best : Int) (left_value : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH5 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH6 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : ((left + len) <= n_pre)) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split <= right)) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH15 : (2 <= interval_sum)) (PreH16 : (interval_sum <= 8000)) (PreH17 : ((0 : Int) <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitProgress stones_l dp_l n_pre len left split best)) (PreH20 : (split < right)) (PreH21 : (left_value = (Znth split (Znth left dp_l __default__List_Z) (0 : Int)))) ,
  ((( &( "candidate" ) )) # Int |->_)
  ** (((( &( "dp" ) ) + ((((split + 1) * n_pre) + right) * sizeof(INT)))) # Int |-> ((Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (( &( "dp" ) ) + (((split + 1) * n_pre) * sizeof(INT))) right (0 : Int) n_pre (Znth (split + 1) dp_l __default__List_Z))
  ** (intArray2.missing_i ( &( "dp" ) ) (split + 1) (0 : Int) n_pre n_pre dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))))
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "interval_sum" ) )) # Int |-> (interval_sum))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ ((left_value + (Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))) <= INT_MAX) ”

noncomputable def mergingStones_safety_wit_36_split_goal_2 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (dp_l : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (interval_sum : Int) (best : Int) (left_value : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH5 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH6 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : ((left + len) <= n_pre)) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split <= right)) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH15 : (2 <= interval_sum)) (PreH16 : (interval_sum <= 8000)) (PreH17 : ((0 : Int) <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitProgress stones_l dp_l n_pre len left split best)) (PreH20 : (split < right)) (PreH21 : (left_value = (Znth split (Znth left dp_l __default__List_Z) (0 : Int)))) ,
  ((( &( "candidate" ) )) # Int |->_)
  ** (((( &( "dp" ) ) + ((((split + 1) * n_pre) + right) * sizeof(INT)))) # Int |-> ((Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (( &( "dp" ) ) + (((split + 1) * n_pre) * sizeof(INT))) right (0 : Int) n_pre (Znth (split + 1) dp_l __default__List_Z))
  ** (intArray2.missing_i ( &( "dp" ) ) (split + 1) (0 : Int) n_pre n_pre dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))))
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "interval_sum" ) )) # Int |-> (interval_sum))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** ((( &( "left_value" ) )) # Int |-> (left_value))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ ((INT_MIN) <= (left_value + (Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int))))) ”

noncomputable def mergingStones_safety_wit_37 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (dp_l : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (interval_sum : Int) (best : Int) (left_value : Int) (__default__List_Z : _List_Z) (PreH1 : (((left_value + (Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))) + interval_sum) < best)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : ((left + len) <= n_pre)) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left <= split)) (PreH14 : (split <= right)) (PreH15 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH16 : (2 <= interval_sum)) (PreH17 : (interval_sum <= 8000)) (PreH18 : ((0 : Int) <= best)) (PreH19 : (best <= 1000000)) (PreH20 : (StoneSplitProgress stones_l dp_l n_pre len left split best)) (PreH21 : (split < right)) (PreH22 : (left_value = (Znth split (Znth left dp_l __default__List_Z) (0 : Int)))) ,
  (((( &( "dp" ) ) + ((((split + 1) * n_pre) + right) * sizeof(INT)))) # Int |-> ((Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (( &( "dp" ) ) + (((split + 1) * n_pre) * sizeof(INT))) right (0 : Int) n_pre (Znth (split + 1) dp_l __default__List_Z))
  ** (intArray2.missing_i ( &( "dp" ) ) (split + 1) (0 : Int) n_pre n_pre dp_l)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "interval_sum" ) )) # Int |-> (interval_sum))
  ** ((( &( "best" ) )) # Int |-> (((left_value + (Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))) + interval_sum)))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ ((split + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (split + 1)) ”

noncomputable def mergingStones_safety_wit_38 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (dp_l : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (interval_sum : Int) (best : Int) (left_value : Int) (__default__List_Z : _List_Z) (PreH1 : (((left_value + (Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))) + interval_sum) >= best)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : ((left + len) <= n_pre)) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left <= split)) (PreH14 : (split <= right)) (PreH15 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH16 : (2 <= interval_sum)) (PreH17 : (interval_sum <= 8000)) (PreH18 : ((0 : Int) <= best)) (PreH19 : (best <= 1000000)) (PreH20 : (StoneSplitProgress stones_l dp_l n_pre len left split best)) (PreH21 : (split < right)) (PreH22 : (left_value = (Znth split (Znth left dp_l __default__List_Z) (0 : Int)))) ,
  (((( &( "dp" ) ) + ((((split + 1) * n_pre) + right) * sizeof(INT)))) # Int |-> ((Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (( &( "dp" ) ) + (((split + 1) * n_pre) * sizeof(INT))) right (0 : Int) n_pre (Znth (split + 1) dp_l __default__List_Z))
  ** (intArray2.missing_i ( &( "dp" ) ) (split + 1) (0 : Int) n_pre n_pre dp_l)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "interval_sum" ) )) # Int |-> (interval_sum))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ ((split + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (split + 1)) ”

noncomputable def mergingStones_safety_wit_39 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (best : Int) (interval_sum : Int) (split : Int) (right : Int) (left : Int) (len : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (PreH1 : (split >= right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : ((left + len) <= n_pre)) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left <= split)) (PreH14 : (split <= right)) (PreH15 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH16 : (2 <= interval_sum)) (PreH17 : (interval_sum <= 8000)) (PreH18 : ((0 : Int) <= best)) (PreH19 : (best <= 1000000)) (PreH20 : (StoneSplitProgress stones_l dp_l n_pre len left split best)) ,
  ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "interval_sum" ) )) # Int |-> (interval_sum))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ ((left * n_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left * n_pre)) ”

noncomputable def mergingStones_safety_wit_40 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (best : Int) (interval_sum : Int) (split : Int) (right : Int) (left : Int) (len : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (PreH1 : (split >= right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : ((left + len) <= n_pre)) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left <= split)) (PreH14 : (split <= right)) (PreH15 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH16 : (2 <= interval_sum)) (PreH17 : (interval_sum <= 8000)) (PreH18 : ((0 : Int) <= best)) (PreH19 : (best <= 1000000)) (PreH20 : (StoneSplitProgress stones_l dp_l n_pre len left split best)) ,
  ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "interval_sum" ) )) # Int |-> (interval_sum))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def mergingStones_safety_wit_41 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (best : Int) (interval_sum : Int) (split : Int) (right : Int) (left : Int) (len : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (split >= right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : ((left + len) <= n_pre)) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left <= split)) (PreH14 : (split <= right)) (PreH15 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH16 : (2 <= interval_sum)) (PreH17 : (interval_sum <= 8000)) (PreH18 : ((0 : Int) <= best)) (PreH19 : (best <= 1000000)) (PreH20 : (StoneSplitProgress stones_l dp_l n_pre len left split best)) ,
  (((( &( "dp" ) ) + (((left * n_pre) + right) * sizeof(INT)))) # Int |-> (best))
  ** (intArray.missing_i (( &( "dp" ) ) + ((left * n_pre) * sizeof(INT))) right (0 : Int) n_pre (Znth left dp_l __default__List_Z))
  ** (intArray2.missing_i ( &( "dp" ) ) left (0 : Int) n_pre n_pre dp_l)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ ((left + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left + 1)) ”

noncomputable def mergingStones_safety_wit_42 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (left : Int) (len : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (PreH1 : ((left + len) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= ((n_pre - len) + 1))) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left)) ,
  ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ ((len + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (len + 1)) ”

noncomputable def mergingStones_safety_wit_43 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (len : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (PreH1 : (len > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1))) (PreH10 : (StoneLenDone stones_l dp_l n_pre len)) ,
  ((( &( "result" ) )) # Int |->_)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ ((n_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre - 1)) ”

noncomputable def mergingStones_safety_wit_44 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (len : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (PreH1 : (len > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1))) (PreH10 : (StoneLenDone stones_l dp_l n_pre len)) ,
  ((( &( "result" ) )) # Int |->_)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ (((0 : Int) * n_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((0 : Int) * n_pre)) ”

noncomputable def mergingStones_safety_wit_45 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (len : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (PreH1 : (len > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1))) (PreH10 : (StoneLenDone stones_l dp_l n_pre len)) ,
  ((( &( "result" ) )) # Int |->_)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def mergingStones_safety_wit_46 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (len : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (PreH1 : (len > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1))) (PreH10 : (StoneLenDone stones_l dp_l n_pre len)) ,
  ((( &( "result" ) )) # Int |->_)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def mergingStones_safety_wit_47 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (len : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (PreH1 : (len > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1))) (PreH10 : (StoneLenDone stones_l dp_l n_pre len)) ,
  ((( &( "result" ) )) # Int |->_)
  ** ((( &( "stones" ) )) # Ptr |-> (stones_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def mergingStones_entail_wit_1 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (stones_l)) = n_pre)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) ,
  (intArray.undef_full ( &( "dp" ) ) 64)
  ** (intArray.undef_full ( &( "prefix" ) ) 9)
  ** (intArray.full stones_pre n_pre stones_l)
|--
  EX dp_flat : (List Int),
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (n_pre * n_pre)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (stones_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) stones_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) stones_l) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.undef_full ( &( "prefix" ) ) 9)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) (0 : Int) dp_flat)
  ** (intArray.undef_seg ( &( "dp" ) ) (0 : Int) 64)

noncomputable def mergingStones_entail_wit_2 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_flat_2 : (List Int)) (k : Int) (PreH1 : (k < (n_pre * n_pre))) (PreH2 : ((0 : Int) <= k)) (PreH3 : (k <= (n_pre * n_pre))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH8 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) ,
  (intArray.seg ( &( "dp" ) ) (0 : Int) (k + 1) (dp_flat_2 ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "dp" ) ) (k + 1) 64)
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.undef_full ( &( "prefix" ) ) 9)
|--
  EX dp_flat : (List Int),
  “ ((0 : Int) <= (k + 1)) ” &&
  “ ((k + 1) <= (n_pre * n_pre)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (stones_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) stones_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) stones_l) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.undef_full ( &( "prefix" ) ) 9)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) (k + 1) dp_flat)
  ** (intArray.undef_seg ( &( "dp" ) ) (k + 1) 64)

noncomputable def mergingStones_entail_wit_3 : Prop :=
  (
forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_flat : (List Int)) (k : Int) (PreH1 : (k >= (n_pre * n_pre))) (PreH2 : ((0 : Int) <= k)) (PreH3 : (k <= (n_pre * n_pre))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH8 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) ,
  (((( &( "prefix" ) ) + ((0 : Int) * sizeof(INT)))) # Int |-> ((0 : Int)))
  ** (intArray.undef_seg ( &( "prefix" ) ) 1 9)
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) k dp_flat)
  ** (intArray.undef_seg ( &( "dp" ) ) k 64)
|--
  EX prefix_l : (List Int), EX dp_init : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) stones_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) stones_l) ” &&
  “ (Forall (Eq (n_pre)) (List.map (Zlength) (dp_init))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (StonePrefixProgress stones_l prefix_l (0 : Int)) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.seg ( &( "prefix" ) ) (0 : Int) ((0 : Int) + 1) prefix_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) ((0 : Int) + 1) (n_pre + 1))
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_init)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
) \/
(
forall (n_pre : Int) (stones_l : (List Int)) (dp_flat : (List Int)) (k : Int) (PreH1 : ((0 : Int) <= INT_MAX)) (PreH2 : ((0 : Int) >= INT_MIN)) (PreH3 : (k >= (n_pre * n_pre))) (PreH4 : ((0 : Int) <= k)) (PreH5 : (k <= (n_pre * n_pre))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 8)) (PreH8 : ((Zlength (stones_l)) = n_pre)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH10 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) ,
  (((( &( "prefix" ) ) + ((0 : Int) * sizeof(INT)))) # Int |-> ((0 : Int)))
  ** (intArray.undef_seg ( &( "prefix" ) ) 1 9)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) k dp_flat)
|--
  EX prefix_l : (List Int), EX dp_init : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) stones_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) stones_l) ” &&
  “ (Forall (Eq (n_pre)) (List.map (Zlength) (dp_init))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (StonePrefixProgress stones_l prefix_l (0 : Int)) ”
  &&  (intArray.seg ( &( "prefix" ) ) (0 : Int) ((0 : Int) + 1) prefix_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) ((0 : Int) + 1) (n_pre + 1))
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_init)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
)

noncomputable def mergingStones_entail_wit_4 : Prop :=
  (
forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (i : Int) (dp_init_2 : (List (List Int))) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_init_2)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l_2 i)) ,
  (intArray.seg ( &( "prefix" ) ) (0 : Int) ((i + 1) + 1) (prefix_l_2 ++ (((Znth (i - (0 : Int)) prefix_l_2 (0 : Int)) + (Znth i stones_l (0 : Int))) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "prefix" ) ) ((i + 1) + 1) (n_pre + 1))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_init_2)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  EX prefix_l : (List Int), EX dp_init : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) stones_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) stones_l) ” &&
  “ (Forall (Eq (n_pre)) (List.map (Zlength) (dp_init))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ (StonePrefixProgress stones_l prefix_l (i + 1)) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.seg ( &( "prefix" ) ) (0 : Int) ((i + 1) + 1) prefix_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) ((i + 1) + 1) (n_pre + 1))
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_init)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
) \/
(
forall (n_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (i : Int) (dp_init_2 : (List (List Int))) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_init_2)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l_2 i)) ,
  TT && emp 
|--
  “ (StonePrefixProgress stones_l (prefix_l_2 ++ (((Znth (i - (0 : Int)) prefix_l_2 (0 : Int)) + (Znth i stones_l (0 : Int))) :: (@List.nil Int))) (i + 1)) ”
  &&  emp
)

noncomputable def mergingStones_entail_wit_4_split_goal_1 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (i : Int) (dp_init_2 : (List (List Int))) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_init_2)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l_2 i)) ,
  (StonePrefixProgress stones_l (prefix_l_2 ++ (((Znth (i - (0 : Int)) prefix_l_2 (0 : Int)) + (Znth i stones_l (0 : Int))) :: (@List.nil Int))) (i + 1))

noncomputable def mergingStones_entail_wit_5 : Prop :=
  (
forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (i : Int) (dp_init : (List (List Int))) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_init)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l_2 i)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.seg ( &( "prefix" ) ) (0 : Int) (i + 1) prefix_l_2)
  ** (intArray.undef_seg ( &( "prefix" ) ) (i + 1) (n_pre + 1))
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_init)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  EX prefix_l : (List Int), EX dp_l : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) stones_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) stones_l) ” &&
  “ (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l))) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (StoneZeroRows dp_l (0 : Int)) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
) \/
(
forall (n_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (i : Int) (dp_init : (List (List Int))) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_init)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l_2 i)) ,
  TT && emp 
|--
  “ (StoneZeroRows dp_init (0 : Int)) ” &&
  “ (StonePrefixDone stones_l prefix_l_2 n_pre) ”
  &&  emp
)

noncomputable def mergingStones_entail_wit_5_split_goal_1 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (i : Int) (dp_init : (List (List Int))) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_init)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l_2 i)) ,
  (StoneZeroRows dp_init (0 : Int))

noncomputable def mergingStones_entail_wit_5_split_goal_2 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (i : Int) (dp_init : (List (List Int))) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_init)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l_2 i)) ,
  (StonePrefixDone stones_l prefix_l_2 n_pre)

noncomputable def mergingStones_entail_wit_6 : Prop :=
  (
forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (row : Int) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (PreH1 : (row < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l_2)))) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH8 : ((0 : Int) <= row)) (PreH9 : (row <= n_pre)) (PreH10 : (StoneZeroRows dp_l_2 row)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l_2)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l_2)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  EX prefix_l : (List Int), EX dp_l : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) stones_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) stones_l) ” &&
  “ (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l))) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ ((0 : Int) <= row) ” &&
  “ (row < n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (StoneZeroProgress dp_l row (0 : Int)) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
) \/
(
forall (n_pre : Int) (stones_l : (List Int)) (row : Int) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (PreH1 : (row < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l_2)))) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH8 : ((0 : Int) <= row)) (PreH9 : (row <= n_pre)) (PreH10 : (StoneZeroRows dp_l_2 row)) ,
  TT && emp 
|--
  “ (StoneZeroProgress dp_l_2 row (0 : Int)) ”
  &&  emp
)

noncomputable def mergingStones_entail_wit_6_split_goal_1 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (row : Int) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (PreH1 : (row < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l_2)))) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH8 : ((0 : Int) <= row)) (PreH9 : (row <= n_pre)) (PreH10 : (StoneZeroRows dp_l_2 row)) ,
  (StoneZeroProgress dp_l_2 row (0 : Int))

noncomputable def mergingStones_entail_wit_7 : Prop :=
  (
forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (col : Int) (row : Int) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (col < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l_2)))) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH8 : ((0 : Int) <= row)) (PreH9 : (row < n_pre)) (PreH10 : ((0 : Int) <= col)) (PreH11 : (col <= n_pre)) (PreH12 : (StoneZeroProgress dp_l_2 row col)) ,
  (((( &( "dp" ) ) + (((row * n_pre) + col) * sizeof(INT)))) # Int |-> ((0 : Int)))
  ** (intArray.missing_i (( &( "dp" ) ) + ((row * n_pre) * sizeof(INT))) col (0 : Int) n_pre (Znth row dp_l_2 __default__List_Z))
  ** (intArray2.missing_i ( &( "dp" ) ) row (0 : Int) n_pre n_pre dp_l_2)
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l_2)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  EX prefix_l : (List Int), EX dp_l : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) stones_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) stones_l) ” &&
  “ (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l))) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ ((0 : Int) <= row) ” &&
  “ (row < n_pre) ” &&
  “ ((0 : Int) <= (col + 1)) ” &&
  “ ((col + 1) <= n_pre) ” &&
  “ (StoneZeroProgress dp_l row (col + 1)) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
) \/
(
forall (n_pre : Int) (stones_l : (List Int)) (col : Int) (row : Int) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : ((0 : Int) <= INT_MAX)) (PreH2 : ((0 : Int) >= INT_MIN)) (PreH3 : (col < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH8 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l_2)))) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH10 : ((0 : Int) <= row)) (PreH11 : (row < n_pre)) (PreH12 : ((0 : Int) <= col)) (PreH13 : (col <= n_pre)) (PreH14 : (StoneZeroProgress dp_l_2 row col)) ,
  (((( &( "dp" ) ) + (((row * n_pre) + col) * sizeof(INT)))) # Int |-> ((0 : Int)))
  ** (intArray.missing_i (( &( "dp" ) ) + ((row * n_pre) * sizeof(INT))) col (0 : Int) n_pre (Znth row dp_l_2 __default__List_Z))
  ** (intArray2.missing_i ( &( "dp" ) ) row (0 : Int) n_pre n_pre dp_l_2)
|--
  EX dp_l : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) stones_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) stones_l) ” &&
  “ (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l))) ” &&
  “ (StonePrefixDone stones_l prefix_l_2 n_pre) ” &&
  “ ((0 : Int) <= row) ” &&
  “ (row < n_pre) ” &&
  “ ((0 : Int) <= (col + 1)) ” &&
  “ ((col + 1) <= n_pre) ” &&
  “ (StoneZeroProgress dp_l row (col + 1)) ”
  &&  (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
)

noncomputable def mergingStones_entail_wit_8 : Prop :=
  (
forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (col : Int) (row : Int) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (PreH1 : (col >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l_2)))) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH8 : ((0 : Int) <= row)) (PreH9 : (row < n_pre)) (PreH10 : ((0 : Int) <= col)) (PreH11 : (col <= n_pre)) (PreH12 : (StoneZeroProgress dp_l_2 row col)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l_2)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l_2)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  EX prefix_l : (List Int), EX dp_l : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) stones_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) stones_l) ” &&
  “ (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l))) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ ((0 : Int) <= (row + 1)) ” &&
  “ ((row + 1) <= n_pre) ” &&
  “ (StoneZeroRows dp_l (row + 1)) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
) \/
(
forall (n_pre : Int) (stones_l : (List Int)) (col : Int) (row : Int) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (PreH1 : (col >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l_2)))) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH8 : ((0 : Int) <= row)) (PreH9 : (row < n_pre)) (PreH10 : ((0 : Int) <= col)) (PreH11 : (col <= n_pre)) (PreH12 : (StoneZeroProgress dp_l_2 row col)) ,
  TT && emp 
|--
  “ (StoneZeroRows dp_l_2 (row + 1)) ”
  &&  emp
)

noncomputable def mergingStones_entail_wit_8_split_goal_1 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (col : Int) (row : Int) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (PreH1 : (col >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l_2)))) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH8 : ((0 : Int) <= row)) (PreH9 : (row < n_pre)) (PreH10 : ((0 : Int) <= col)) (PreH11 : (col <= n_pre)) (PreH12 : (StoneZeroProgress dp_l_2 row col)) ,
  (StoneZeroRows dp_l_2 (row + 1))

noncomputable def mergingStones_entail_wit_9 : Prop :=
  (
forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (row : Int) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (PreH1 : (row >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l_2)))) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH8 : ((0 : Int) <= row)) (PreH9 : (row <= n_pre)) (PreH10 : (StoneZeroRows dp_l_2 row)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l_2)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l_2)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  EX prefix_l : (List Int), EX dp_l : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) stones_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) stones_l) ” &&
  “ (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l))) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (2 <= 2) ” &&
  “ (2 <= (n_pre + 1)) ” &&
  “ (StoneLenDone stones_l dp_l n_pre 2) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
) \/
(
forall (n_pre : Int) (stones_l : (List Int)) (row : Int) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (PreH1 : (row >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l_2)))) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH8 : ((0 : Int) <= row)) (PreH9 : (row <= n_pre)) (PreH10 : (StoneZeroRows dp_l_2 row)) ,
  TT && emp 
|--
  “ (StoneLenDone stones_l dp_l_2 n_pre 2) ”
  &&  emp
)

noncomputable def mergingStones_entail_wit_9_split_goal_1 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (row : Int) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (PreH1 : (row >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l_2)))) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH8 : ((0 : Int) <= row)) (PreH9 : (row <= n_pre)) (PreH10 : (StoneZeroRows dp_l_2 row)) ,
  (StoneLenDone stones_l dp_l_2 n_pre 2)

noncomputable def mergingStones_entail_wit_10 : Prop :=
  (
forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (len : Int) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (PreH1 : (len <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l_2)))) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1))) (PreH10 : (StoneLenDone stones_l dp_l_2 n_pre len)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l_2)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l_2)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  EX prefix_l : (List Int), EX dp_l : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) stones_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) stones_l) ” &&
  “ (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l))) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= ((n_pre - len) + 1)) ” &&
  “ (StoneLeftProgress stones_l dp_l n_pre len (0 : Int)) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
) \/
(
forall (n_pre : Int) (stones_l : (List Int)) (len : Int) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (PreH1 : (len <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l_2)))) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1))) (PreH10 : (StoneLenDone stones_l dp_l_2 n_pre len)) ,
  TT && emp 
|--
  “ (StoneLeftProgress stones_l dp_l_2 n_pre len (0 : Int)) ”
  &&  emp
)

noncomputable def mergingStones_entail_wit_10_split_goal_1 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (len : Int) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (PreH1 : (len <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l_2)))) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1))) (PreH10 : (StoneLenDone stones_l dp_l_2 n_pre len)) ,
  (StoneLeftProgress stones_l dp_l_2 n_pre len (0 : Int))

noncomputable def mergingStones_entail_wit_11 : Prop :=
  (
forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (left : Int) (len : Int) (prefix_l : (List Int)) (dp_l_2 : (List (List Int))) (PreH1 : ((left + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l_2)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= ((n_pre - len) + 1))) (PreH12 : (StoneLeftProgress stones_l dp_l_2 n_pre len left)) ,
  (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l_2)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  EX prefix_l_2 : (List Int), EX dp_l : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) stones_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) stones_l) ” &&
  “ (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l))) ” &&
  “ (StonePrefixDone stones_l prefix_l_2 n_pre) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + len) <= n_pre) ” &&
  “ (((left + len) - 1) = ((left + len) - 1)) ” &&
  “ (left <= left) ” &&
  “ (left <= ((left + len) - 1)) ” &&
  “ (((Znth (((left + len) - 1) + 1) prefix_l (0 : Int)) - (Znth left prefix_l (0 : Int))) = (sum ((sublist (left) ((((left + len) - 1) + 1)) (stones_l))))) ” &&
  “ (2 <= ((Znth (((left + len) - 1) + 1) prefix_l (0 : Int)) - (Znth left prefix_l (0 : Int)))) ” &&
  “ (((Znth (((left + len) - 1) + 1) prefix_l (0 : Int)) - (Znth left prefix_l (0 : Int))) <= 8000) ” &&
  “ ((0 : Int) <= 1000000) ” &&
  “ (1000000 <= 1000000) ” &&
  “ (StoneSplitProgress stones_l dp_l n_pre len left left 1000000) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l_2)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
) \/
(
forall (n_pre : Int) (stones_l : (List Int)) (left : Int) (len : Int) (prefix_l : (List Int)) (dp_l_2 : (List (List Int))) (PreH1 : ((left + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l_2)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= ((n_pre - len) + 1))) (PreH12 : (StoneLeftProgress stones_l dp_l_2 n_pre len left)) ,
  TT && emp 
|--
  “ (StoneSplitProgress stones_l dp_l_2 n_pre len left left 1000000) ” &&
  “ (((Znth (((left + len) - 1) + 1) prefix_l (0 : Int)) - (Znth left prefix_l (0 : Int))) <= 8000) ” &&
  “ (2 <= ((Znth (((left + len) - 1) + 1) prefix_l (0 : Int)) - (Znth left prefix_l (0 : Int)))) ” &&
  “ (((Znth (((left + len) - 1) + 1) prefix_l (0 : Int)) - (Znth left prefix_l (0 : Int))) = (sum ((sublist (left) ((((left + len) - 1) + 1)) (stones_l))))) ”
  &&  emp
)

noncomputable def mergingStones_entail_wit_11_split_goal_1 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (left : Int) (len : Int) (prefix_l : (List Int)) (dp_l_2 : (List (List Int))) (PreH1 : ((left + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l_2)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= ((n_pre - len) + 1))) (PreH12 : (StoneLeftProgress stones_l dp_l_2 n_pre len left)) ,
  (StoneSplitProgress stones_l dp_l_2 n_pre len left left 1000000)

noncomputable def mergingStones_entail_wit_11_split_goal_2 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (left : Int) (len : Int) (prefix_l : (List Int)) (dp_l_2 : (List (List Int))) (PreH1 : ((left + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l_2)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= ((n_pre - len) + 1))) (PreH12 : (StoneLeftProgress stones_l dp_l_2 n_pre len left)) ,
  (((Znth (((left + len) - 1) + 1) prefix_l (0 : Int)) - (Znth left prefix_l (0 : Int))) <= 8000)

noncomputable def mergingStones_entail_wit_11_split_goal_3 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (left : Int) (len : Int) (prefix_l : (List Int)) (dp_l_2 : (List (List Int))) (PreH1 : ((left + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l_2)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= ((n_pre - len) + 1))) (PreH12 : (StoneLeftProgress stones_l dp_l_2 n_pre len left)) ,
  (2 <= ((Znth (((left + len) - 1) + 1) prefix_l (0 : Int)) - (Znth left prefix_l (0 : Int))))

noncomputable def mergingStones_entail_wit_11_split_goal_4 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (left : Int) (len : Int) (prefix_l : (List Int)) (dp_l_2 : (List (List Int))) (PreH1 : ((left + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l_2)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= ((n_pre - len) + 1))) (PreH12 : (StoneLeftProgress stones_l dp_l_2 n_pre len left)) ,
  (((Znth (((left + len) - 1) + 1) prefix_l (0 : Int)) - (Znth left prefix_l (0 : Int))) = (sum ((sublist (left) ((((left + len) - 1) + 1)) (stones_l)))))

noncomputable def mergingStones_entail_wit_12 : Prop :=
  (
forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (best : Int) (interval_sum : Int) (split : Int) (right : Int) (left : Int) (len : Int) (prefix_l_2 : (List Int)) (dp_l : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (split < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : ((left + len) <= n_pre)) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left <= split)) (PreH14 : (split <= right)) (PreH15 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH16 : (2 <= interval_sum)) (PreH17 : (interval_sum <= 8000)) (PreH18 : ((0 : Int) <= best)) (PreH19 : (best <= 1000000)) (PreH20 : (StoneSplitProgress stones_l dp_l n_pre len left split best)) ,
  (((( &( "dp" ) ) + (((left * n_pre) + split) * sizeof(INT)))) # Int |-> ((Znth (split) ((Znth left dp_l __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (( &( "dp" ) ) + ((left * n_pre) * sizeof(INT))) split (0 : Int) n_pre (Znth left dp_l __default__List_Z))
  ** (intArray2.missing_i ( &( "dp" ) ) left (0 : Int) n_pre n_pre dp_l)
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l_2)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  EX prefix_l : (List Int), EX dp_l_2 : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) stones_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) stones_l) ” &&
  “ (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l_2))) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + len) <= n_pre) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left <= split) ” &&
  “ (split <= right) ” &&
  “ (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l))))) ” &&
  “ (2 <= interval_sum) ” &&
  “ (interval_sum <= 8000) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 1000000) ” &&
  “ (StoneSplitProgress stones_l dp_l_2 n_pre len left split best) ” &&
  “ (split < right) ” &&
  “ ((Znth (split) ((Znth left dp_l __default__List_Z)) ((0 : Int))) = (Znth split (Znth left dp_l_2 __default__List_Z) (0 : Int))) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l_2)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
) \/
(
forall (n_pre : Int) (stones_l : (List Int)) (best : Int) (interval_sum : Int) (split : Int) (right : Int) (left : Int) (len : Int) (prefix_l_2 : (List Int)) (dp_l : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : ((Znth (split) ((Znth left dp_l __default__List_Z)) ((0 : Int))) <= INT_MAX)) (PreH2 : ((Znth (split) ((Znth left dp_l __default__List_Z)) ((0 : Int))) >= INT_MIN)) (PreH3 : (split < right)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH8 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH10 : (2 <= len)) (PreH11 : (len <= n_pre)) (PreH12 : ((0 : Int) <= left)) (PreH13 : ((left + len) <= n_pre)) (PreH14 : (right = ((left + len) - 1))) (PreH15 : (left <= split)) (PreH16 : (split <= right)) (PreH17 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH18 : (2 <= interval_sum)) (PreH19 : (interval_sum <= 8000)) (PreH20 : ((0 : Int) <= best)) (PreH21 : (best <= 1000000)) (PreH22 : (StoneSplitProgress stones_l dp_l n_pre len left split best)) ,
  (((( &( "dp" ) ) + (((left * n_pre) + split) * sizeof(INT)))) # Int |-> ((Znth (split) ((Znth left dp_l __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (( &( "dp" ) ) + ((left * n_pre) * sizeof(INT))) split (0 : Int) n_pre (Znth left dp_l __default__List_Z))
  ** (intArray2.missing_i ( &( "dp" ) ) left (0 : Int) n_pre n_pre dp_l)
|--
  EX dp_l_2 : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) stones_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) stones_l) ” &&
  “ (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l_2))) ” &&
  “ (StonePrefixDone stones_l prefix_l_2 n_pre) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + len) <= n_pre) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left <= split) ” &&
  “ (split <= right) ” &&
  “ (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l))))) ” &&
  “ (2 <= interval_sum) ” &&
  “ (interval_sum <= 8000) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 1000000) ” &&
  “ (StoneSplitProgress stones_l dp_l_2 n_pre len left split best) ” &&
  “ (split < right) ” &&
  “ ((Znth (split) ((Znth left dp_l __default__List_Z)) ((0 : Int))) = (Znth split (Znth left dp_l_2 __default__List_Z) (0 : Int))) ”
  &&  (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l_2)
)

noncomputable def mergingStones_entail_wit_13_1 : Prop :=
  (
forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (interval_sum : Int) (best : Int) (left_value : Int) (__default__List_Z : _List_Z) (PreH1 : (((left_value + (Znth (right) ((Znth (split + 1) dp_l_2 __default__List_Z)) ((0 : Int)))) + interval_sum) < best)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l_2)))) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : ((left + len) <= n_pre)) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left <= split)) (PreH14 : (split <= right)) (PreH15 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH16 : (2 <= interval_sum)) (PreH17 : (interval_sum <= 8000)) (PreH18 : ((0 : Int) <= best)) (PreH19 : (best <= 1000000)) (PreH20 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best)) (PreH21 : (split < right)) (PreH22 : (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) (0 : Int)))) ,
  (((( &( "dp" ) ) + ((((split + 1) * n_pre) + right) * sizeof(INT)))) # Int |-> ((Znth (right) ((Znth (split + 1) dp_l_2 __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (( &( "dp" ) ) + (((split + 1) * n_pre) * sizeof(INT))) right (0 : Int) n_pre (Znth (split + 1) dp_l_2 __default__List_Z))
  ** (intArray2.missing_i ( &( "dp" ) ) (split + 1) (0 : Int) n_pre n_pre dp_l_2)
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l_2)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  EX prefix_l : (List Int), EX dp_l : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) stones_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) stones_l) ” &&
  “ (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l))) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + len) <= n_pre) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left <= (split + 1)) ” &&
  “ ((split + 1) <= right) ” &&
  “ (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l))))) ” &&
  “ (2 <= interval_sum) ” &&
  “ (interval_sum <= 8000) ” &&
  “ ((0 : Int) <= ((left_value + (Znth (right) ((Znth (split + 1) dp_l_2 __default__List_Z)) ((0 : Int)))) + interval_sum)) ” &&
  “ (((left_value + (Znth (right) ((Znth (split + 1) dp_l_2 __default__List_Z)) ((0 : Int)))) + interval_sum) <= 1000000) ” &&
  “ (StoneSplitProgress stones_l dp_l n_pre len left (split + 1) ((left_value + (Znth (right) ((Znth (split + 1) dp_l_2 __default__List_Z)) ((0 : Int)))) + interval_sum)) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
) \/
(
forall (n_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (interval_sum : Int) (best : Int) (left_value : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth (right) ((Znth (split + 1) dp_l_2 __default__List_Z)) ((0 : Int))) <= INT_MAX)) (PreH2 : ((Znth (right) ((Znth (split + 1) dp_l_2 __default__List_Z)) ((0 : Int))) >= INT_MIN)) (PreH3 : (((left_value + (Znth (right) ((Znth (split + 1) dp_l_2 __default__List_Z)) ((0 : Int)))) + interval_sum) < best)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH8 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l_2)))) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH10 : (2 <= len)) (PreH11 : (len <= n_pre)) (PreH12 : ((0 : Int) <= left)) (PreH13 : ((left + len) <= n_pre)) (PreH14 : (right = ((left + len) - 1))) (PreH15 : (left <= split)) (PreH16 : (split <= right)) (PreH17 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH18 : (2 <= interval_sum)) (PreH19 : (interval_sum <= 8000)) (PreH20 : ((0 : Int) <= best)) (PreH21 : (best <= 1000000)) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best)) (PreH23 : (split < right)) (PreH24 : (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) (0 : Int)))) ,
  (((( &( "dp" ) ) + ((((split + 1) * n_pre) + right) * sizeof(INT)))) # Int |-> ((Znth (right) ((Znth (split + 1) dp_l_2 __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (( &( "dp" ) ) + (((split + 1) * n_pre) * sizeof(INT))) right (0 : Int) n_pre (Znth (split + 1) dp_l_2 __default__List_Z))
  ** (intArray2.missing_i ( &( "dp" ) ) (split + 1) (0 : Int) n_pre n_pre dp_l_2)
|--
  EX dp_l : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) stones_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) stones_l) ” &&
  “ (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l))) ” &&
  “ (StonePrefixDone stones_l prefix_l_2 n_pre) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + len) <= n_pre) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left <= (split + 1)) ” &&
  “ ((split + 1) <= right) ” &&
  “ (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l))))) ” &&
  “ (2 <= interval_sum) ” &&
  “ (interval_sum <= 8000) ” &&
  “ ((0 : Int) <= ((left_value + (Znth (right) ((Znth (split + 1) dp_l_2 __default__List_Z)) ((0 : Int)))) + interval_sum)) ” &&
  “ (((left_value + (Znth (right) ((Znth (split + 1) dp_l_2 __default__List_Z)) ((0 : Int)))) + interval_sum) <= 1000000) ” &&
  “ (StoneSplitProgress stones_l dp_l n_pre len left (split + 1) ((left_value + (Znth (right) ((Znth (split + 1) dp_l_2 __default__List_Z)) ((0 : Int)))) + interval_sum)) ”
  &&  (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
)

noncomputable def mergingStones_entail_wit_13_2 : Prop :=
  (
forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (interval_sum : Int) (best : Int) (left_value : Int) (__default__List_Z : _List_Z) (PreH1 : (((left_value + (Znth (right) ((Znth (split + 1) dp_l_2 __default__List_Z)) ((0 : Int)))) + interval_sum) >= best)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l_2)))) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : ((left + len) <= n_pre)) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left <= split)) (PreH14 : (split <= right)) (PreH15 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH16 : (2 <= interval_sum)) (PreH17 : (interval_sum <= 8000)) (PreH18 : ((0 : Int) <= best)) (PreH19 : (best <= 1000000)) (PreH20 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best)) (PreH21 : (split < right)) (PreH22 : (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) (0 : Int)))) ,
  (((( &( "dp" ) ) + ((((split + 1) * n_pre) + right) * sizeof(INT)))) # Int |-> ((Znth (right) ((Znth (split + 1) dp_l_2 __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (( &( "dp" ) ) + (((split + 1) * n_pre) * sizeof(INT))) right (0 : Int) n_pre (Znth (split + 1) dp_l_2 __default__List_Z))
  ** (intArray2.missing_i ( &( "dp" ) ) (split + 1) (0 : Int) n_pre n_pre dp_l_2)
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l_2)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  EX prefix_l : (List Int), EX dp_l : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) stones_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) stones_l) ” &&
  “ (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l))) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + len) <= n_pre) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left <= (split + 1)) ” &&
  “ ((split + 1) <= right) ” &&
  “ (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l))))) ” &&
  “ (2 <= interval_sum) ” &&
  “ (interval_sum <= 8000) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 1000000) ” &&
  “ (StoneSplitProgress stones_l dp_l n_pre len left (split + 1) best) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
) \/
(
forall (n_pre : Int) (stones_l : (List Int)) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (interval_sum : Int) (best : Int) (left_value : Int) (__default__List_Z : _List_Z) (PreH1 : ((Znth (right) ((Znth (split + 1) dp_l_2 __default__List_Z)) ((0 : Int))) <= INT_MAX)) (PreH2 : ((Znth (right) ((Znth (split + 1) dp_l_2 __default__List_Z)) ((0 : Int))) >= INT_MIN)) (PreH3 : (((left_value + (Znth (right) ((Znth (split + 1) dp_l_2 __default__List_Z)) ((0 : Int)))) + interval_sum) >= best)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH8 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l_2)))) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH10 : (2 <= len)) (PreH11 : (len <= n_pre)) (PreH12 : ((0 : Int) <= left)) (PreH13 : ((left + len) <= n_pre)) (PreH14 : (right = ((left + len) - 1))) (PreH15 : (left <= split)) (PreH16 : (split <= right)) (PreH17 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH18 : (2 <= interval_sum)) (PreH19 : (interval_sum <= 8000)) (PreH20 : ((0 : Int) <= best)) (PreH21 : (best <= 1000000)) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best)) (PreH23 : (split < right)) (PreH24 : (left_value = (Znth split (Znth left dp_l_2 __default__List_Z) (0 : Int)))) ,
  (((( &( "dp" ) ) + ((((split + 1) * n_pre) + right) * sizeof(INT)))) # Int |-> ((Znth (right) ((Znth (split + 1) dp_l_2 __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (( &( "dp" ) ) + (((split + 1) * n_pre) * sizeof(INT))) right (0 : Int) n_pre (Znth (split + 1) dp_l_2 __default__List_Z))
  ** (intArray2.missing_i ( &( "dp" ) ) (split + 1) (0 : Int) n_pre n_pre dp_l_2)
|--
  EX dp_l : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) stones_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) stones_l) ” &&
  “ (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l))) ” &&
  “ (StonePrefixDone stones_l prefix_l_2 n_pre) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + len) <= n_pre) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left <= (split + 1)) ” &&
  “ ((split + 1) <= right) ” &&
  “ (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l))))) ” &&
  “ (2 <= interval_sum) ” &&
  “ (interval_sum <= 8000) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 1000000) ” &&
  “ (StoneSplitProgress stones_l dp_l n_pre len left (split + 1) best) ”
  &&  (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
)

noncomputable def mergingStones_entail_wit_14 : Prop :=
  (
forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (best : Int) (interval_sum : Int) (split : Int) (right : Int) (left : Int) (len : Int) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (split >= right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l_2)))) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : ((left + len) <= n_pre)) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left <= split)) (PreH14 : (split <= right)) (PreH15 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH16 : (2 <= interval_sum)) (PreH17 : (interval_sum <= 8000)) (PreH18 : ((0 : Int) <= best)) (PreH19 : (best <= 1000000)) (PreH20 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best)) ,
  (((( &( "dp" ) ) + (((left * n_pre) + right) * sizeof(INT)))) # Int |-> (best))
  ** (intArray.missing_i (( &( "dp" ) ) + ((left * n_pre) * sizeof(INT))) right (0 : Int) n_pre (Znth left dp_l_2 __default__List_Z))
  ** (intArray2.missing_i ( &( "dp" ) ) left (0 : Int) n_pre n_pre dp_l_2)
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l_2)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  EX prefix_l : (List Int), EX dp_l : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) stones_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) stones_l) ” &&
  “ (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l))) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= (left + 1)) ” &&
  “ ((left + 1) <= ((n_pre - len) + 1)) ” &&
  “ (StoneLeftProgress stones_l dp_l n_pre len (left + 1)) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
) \/
(
forall (n_pre : Int) (stones_l : (List Int)) (best : Int) (interval_sum : Int) (split : Int) (right : Int) (left : Int) (len : Int) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (best <= INT_MAX)) (PreH2 : (best >= INT_MIN)) (PreH3 : (split >= right)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH8 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l_2)))) (PreH9 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH10 : (2 <= len)) (PreH11 : (len <= n_pre)) (PreH12 : ((0 : Int) <= left)) (PreH13 : ((left + len) <= n_pre)) (PreH14 : (right = ((left + len) - 1))) (PreH15 : (left <= split)) (PreH16 : (split <= right)) (PreH17 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH18 : (2 <= interval_sum)) (PreH19 : (interval_sum <= 8000)) (PreH20 : ((0 : Int) <= best)) (PreH21 : (best <= 1000000)) (PreH22 : (StoneSplitProgress stones_l dp_l_2 n_pre len left split best)) ,
  (((( &( "dp" ) ) + (((left * n_pre) + right) * sizeof(INT)))) # Int |-> (best))
  ** (intArray.missing_i (( &( "dp" ) ) + ((left * n_pre) * sizeof(INT))) right (0 : Int) n_pre (Znth left dp_l_2 __default__List_Z))
  ** (intArray2.missing_i ( &( "dp" ) ) left (0 : Int) n_pre n_pre dp_l_2)
|--
  EX dp_l : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) stones_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) stones_l) ” &&
  “ (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l))) ” &&
  “ (StonePrefixDone stones_l prefix_l_2 n_pre) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= (left + 1)) ” &&
  “ ((left + 1) <= ((n_pre - len) + 1)) ” &&
  “ (StoneLeftProgress stones_l dp_l n_pre len (left + 1)) ”
  &&  (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
)

noncomputable def mergingStones_entail_wit_15 : Prop :=
  (
forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (left : Int) (len : Int) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (PreH1 : ((left + len) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l_2)))) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= ((n_pre - len) + 1))) (PreH12 : (StoneLeftProgress stones_l dp_l_2 n_pre len left)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l_2)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l_2)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  EX prefix_l : (List Int), EX dp_l : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) stones_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) stones_l) ” &&
  “ (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l))) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (2 <= (len + 1)) ” &&
  “ ((len + 1) <= (n_pre + 1)) ” &&
  “ (StoneLenDone stones_l dp_l n_pre (len + 1)) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
) \/
(
forall (n_pre : Int) (stones_l : (List Int)) (left : Int) (len : Int) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (PreH1 : ((left + len) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l_2)))) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= ((n_pre - len) + 1))) (PreH12 : (StoneLeftProgress stones_l dp_l_2 n_pre len left)) ,
  TT && emp 
|--
  “ (StoneLenDone stones_l dp_l_2 n_pre (len + 1)) ”
  &&  emp
)

noncomputable def mergingStones_entail_wit_15_split_goal_1 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (left : Int) (len : Int) (prefix_l_2 : (List Int)) (dp_l_2 : (List (List Int))) (PreH1 : ((left + len) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l_2)))) (PreH7 : (StonePrefixDone stones_l prefix_l_2 n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= ((n_pre - len) + 1))) (PreH12 : (StoneLeftProgress stones_l dp_l_2 n_pre len left)) ,
  (StoneLenDone stones_l dp_l_2 n_pre (len + 1))

noncomputable def mergingStones_entail_wit_16 : Prop :=
  (
forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (len : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (len > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1))) (PreH10 : (StoneLenDone stones_l dp_l n_pre len)) ,
  (((( &( "dp" ) ) + ((((0 : Int) * n_pre) + (n_pre - 1)) * sizeof(INT)))) # Int |-> ((Znth ((n_pre - 1)) ((Znth (0 : Int) dp_l __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (( &( "dp" ) ) + (((0 : Int) * n_pre) * sizeof(INT))) (n_pre - 1) (0 : Int) n_pre (Znth (0 : Int) dp_l __default__List_Z))
  ** (intArray2.missing_i ( &( "dp" ) ) (0 : Int) (0 : Int) n_pre n_pre dp_l)
  ** ((( &( "width" ) )) # Int |-> (n_pre))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ (StoneMinimumCost stones_l (Znth ((n_pre - 1)) ((Znth (0 : Int) dp_l __default__List_Z)) ((0 : Int)))) ”
  &&  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.undef_full ( &( "prefix" ) ) 9)
  ** (intArray.undef_full ( &( "dp" ) ) 64)
  ** ((( &( "width" ) )) # Int |->_)
) \/
(
forall (n_pre : Int) (stones_l : (List Int)) (len : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : ((Znth ((n_pre - 1)) ((Znth (0 : Int) dp_l __default__List_Z)) ((0 : Int))) <= INT_MAX)) (PreH2 : ((Znth ((n_pre - 1)) ((Znth (0 : Int) dp_l __default__List_Z)) ((0 : Int))) >= INT_MIN)) (PreH3 : (len > n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH8 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH9 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH10 : (2 <= len)) (PreH11 : (len <= (n_pre + 1))) (PreH12 : (StoneLenDone stones_l dp_l n_pre len)) ,
  (((( &( "dp" ) ) + ((((0 : Int) * n_pre) + (n_pre - 1)) * sizeof(INT)))) # Int |-> ((Znth ((n_pre - 1)) ((Znth (0 : Int) dp_l __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (( &( "dp" ) ) + (((0 : Int) * n_pre) * sizeof(INT))) (n_pre - 1) (0 : Int) n_pre (Znth (0 : Int) dp_l __default__List_Z))
  ** (intArray2.missing_i ( &( "dp" ) ) (0 : Int) (0 : Int) n_pre n_pre dp_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ (StoneMinimumCost stones_l (Znth ((n_pre - 1)) ((Znth (0 : Int) dp_l __default__List_Z)) ((0 : Int)))) ”
  &&  (intArray.undef_full ( &( "prefix" ) ) 9)
  ** (intArray.undef_full ( &( "dp" ) ) 64)
)

noncomputable def mergingStones_entail_wit_16_split_goal_1 : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (len : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : ((Znth ((n_pre - 1)) ((Znth (0 : Int) dp_l __default__List_Z)) ((0 : Int))) <= INT_MAX)) (PreH2 : ((Znth ((n_pre - 1)) ((Znth (0 : Int) dp_l __default__List_Z)) ((0 : Int))) >= INT_MIN)) (PreH3 : (len > n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH8 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH9 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH10 : (2 <= len)) (PreH11 : (len <= (n_pre + 1))) (PreH12 : (StoneLenDone stones_l dp_l n_pre len)) ,
  (((( &( "dp" ) ) + ((((0 : Int) * n_pre) + (n_pre - 1)) * sizeof(INT)))) # Int |-> ((Znth ((n_pre - 1)) ((Znth (0 : Int) dp_l __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (( &( "dp" ) ) + (((0 : Int) * n_pre) * sizeof(INT))) (n_pre - 1) (0 : Int) n_pre (Znth (0 : Int) dp_l __default__List_Z))
  ** (intArray2.missing_i ( &( "dp" ) ) (0 : Int) (0 : Int) n_pre n_pre dp_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ (StoneMinimumCost stones_l (Znth ((n_pre - 1)) ((Znth (0 : Int) dp_l __default__List_Z)) ((0 : Int)))) ”

noncomputable def mergingStones_entail_wit_16_split_goal_spatial : Prop :=
  forall (n_pre : Int) (stones_l : (List Int)) (len : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : ((Znth ((n_pre - 1)) ((Znth (0 : Int) dp_l __default__List_Z)) ((0 : Int))) <= INT_MAX)) (PreH2 : ((Znth ((n_pre - 1)) ((Znth (0 : Int) dp_l __default__List_Z)) ((0 : Int))) >= INT_MIN)) (PreH3 : (len > n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH8 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH9 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH10 : (2 <= len)) (PreH11 : (len <= (n_pre + 1))) (PreH12 : (StoneLenDone stones_l dp_l n_pre len)) ,
  (((( &( "dp" ) ) + ((((0 : Int) * n_pre) + (n_pre - 1)) * sizeof(INT)))) # Int |-> ((Znth ((n_pre - 1)) ((Znth (0 : Int) dp_l __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (( &( "dp" ) ) + (((0 : Int) * n_pre) * sizeof(INT))) (n_pre - 1) (0 : Int) n_pre (Znth (0 : Int) dp_l __default__List_Z))
  ** (intArray2.missing_i ( &( "dp" ) ) (0 : Int) (0 : Int) n_pre n_pre dp_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  (intArray.undef_full ( &( "prefix" ) ) 9)
  ** (intArray.undef_full ( &( "dp" ) ) 64)

noncomputable def mergingStones_return_wit_1 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (result : Int) (PreH1 : (StoneMinimumCost stones_l result)) ,
  (intArray.full stones_pre n_pre stones_l)
|--
  “ (StoneMinimumCost stones_l result) ”
  &&  (intArray.full stones_pre n_pre stones_l)

noncomputable def mergingStones_partial_solve_wit_1 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_flat : (List Int)) (k : Int) (PreH1 : (k < (n_pre * n_pre))) (PreH2 : ((0 : Int) <= k)) (PreH3 : (k <= (n_pre * n_pre))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH8 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.undef_full ( &( "prefix" ) ) 9)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) k dp_flat)
  ** (intArray.undef_seg ( &( "dp" ) ) k 64)
|--
  “ (k < (n_pre * n_pre)) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= (n_pre * n_pre)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (stones_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) stones_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) stones_l) ”
  &&  (((( &( "dp" ) ) + (k * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg ( &( "dp" ) ) (k + 1) 64)
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.undef_full ( &( "prefix" ) ) 9)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) k dp_flat)

noncomputable def mergingStones_partial_solve_wit_2 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (dp_flat : (List Int)) (k : Int) (PreH1 : (k >= (n_pre * n_pre))) (PreH2 : ((0 : Int) <= k)) (PreH3 : (k <= (n_pre * n_pre))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (stones_l)) = n_pre)) (PreH7 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH8 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.undef_full ( &( "prefix" ) ) 9)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) k dp_flat)
  ** (intArray.undef_seg ( &( "dp" ) ) k 64)
|--
  “ (k >= (n_pre * n_pre)) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= (n_pre * n_pre)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (stones_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) stones_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) stones_l) ”
  &&  (((( &( "prefix" ) ) + ((0 : Int) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg ( &( "prefix" ) ) 1 9)
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) k dp_flat)
  ** (intArray.undef_seg ( &( "dp" ) ) k 64)

noncomputable def mergingStones_partial_solve_wit_3 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (i : Int) (dp_init : (List (List Int))) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_init)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l i)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.seg ( &( "prefix" ) ) (0 : Int) (i + 1) prefix_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (i + 1) (n_pre + 1))
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_init)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) stones_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) stones_l) ” &&
  “ (Forall (Eq (n_pre)) (List.map (Zlength) (dp_init))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (StonePrefixProgress stones_l prefix_l i) ”
  &&  (((( &( "prefix" ) ) + (i * sizeof(INT)))) # Int |-> ((Znth (i - (0 : Int)) prefix_l (0 : Int))))
  ** (intArray.missing_i ( &( "prefix" ) ) i (0 : Int) (i + 1) prefix_l)
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (i + 1) (n_pre + 1))
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_init)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)

noncomputable def mergingStones_partial_solve_wit_4 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (i : Int) (dp_init : (List (List Int))) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_init)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l i)) ,
  (intArray.seg ( &( "prefix" ) ) (0 : Int) (i + 1) prefix_l)
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (i + 1) (n_pre + 1))
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_init)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) stones_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) stones_l) ” &&
  “ (Forall (Eq (n_pre)) (List.map (Zlength) (dp_init))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (StonePrefixProgress stones_l prefix_l i) ”
  &&  (((stones_pre + (i * sizeof(INT)))) # Int |-> ((Znth i stones_l (0 : Int))))
  ** (intArray.missing_i stones_pre i (0 : Int) n_pre stones_l)
  ** (intArray.seg ( &( "prefix" ) ) (0 : Int) (i + 1) prefix_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (i + 1) (n_pre + 1))
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_init)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)

noncomputable def mergingStones_partial_solve_wit_5 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (i : Int) (dp_init : (List (List Int))) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_init)))) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (StonePrefixProgress stones_l prefix_l i)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.seg ( &( "prefix" ) ) (0 : Int) (i + 1) prefix_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (i + 1) (n_pre + 1))
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_init)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) stones_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) stones_l) ” &&
  “ (Forall (Eq (n_pre)) (List.map (Zlength) (dp_init))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (StonePrefixProgress stones_l prefix_l i) ”
  &&  (((( &( "prefix" ) ) + ((i + 1) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg ( &( "prefix" ) ) ((i + 1) + 1) (n_pre + 1))
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.seg ( &( "prefix" ) ) (0 : Int) (i + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_init)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)

noncomputable def mergingStones_partial_solve_wit_6 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (col : Int) (row : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (col < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : ((0 : Int) <= row)) (PreH9 : (row < n_pre)) (PreH10 : ((0 : Int) <= col)) (PreH11 : (col <= n_pre)) (PreH12 : (StoneZeroProgress dp_l row col)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ (col < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) stones_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) stones_l) ” &&
  “ (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l))) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ ((0 : Int) <= row) ” &&
  “ (row < n_pre) ” &&
  “ ((0 : Int) <= col) ” &&
  “ (col <= n_pre) ” &&
  “ (StoneZeroProgress dp_l row col) ”
  &&  (((( &( "dp" ) ) + (((row * n_pre) + col) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i (( &( "dp" ) ) + ((row * n_pre) * sizeof(INT))) col (0 : Int) n_pre (Znth row dp_l __default__List_Z))
  ** (intArray2.missing_i ( &( "dp" ) ) row (0 : Int) n_pre n_pre dp_l)
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)

noncomputable def mergingStones_partial_solve_wit_7 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (left : Int) (len : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (PreH1 : ((left + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= ((n_pre - len) + 1))) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ ((left + len) <= n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) stones_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) stones_l) ” &&
  “ (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l))) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left <= ((n_pre - len) + 1)) ” &&
  “ (StoneLeftProgress stones_l dp_l n_pre len left) ”
  &&  (((( &( "prefix" ) ) + ((((left + len) - 1) + 1) * sizeof(INT)))) # Int |-> ((Znth (((left + len) - 1) + 1) prefix_l (0 : Int))))
  ** (intArray.missing_i ( &( "prefix" ) ) (((left + len) - 1) + 1) (0 : Int) (n_pre + 1) prefix_l)
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)

noncomputable def mergingStones_partial_solve_wit_8 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (left : Int) (len : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (PreH1 : ((left + len) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= ((n_pre - len) + 1))) (PreH12 : (StoneLeftProgress stones_l dp_l n_pre len left)) ,
  (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ ((left + len) <= n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) stones_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) stones_l) ” &&
  “ (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l))) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left <= ((n_pre - len) + 1)) ” &&
  “ (StoneLeftProgress stones_l dp_l n_pre len left) ”
  &&  (((( &( "prefix" ) ) + (left * sizeof(INT)))) # Int |-> ((Znth left prefix_l (0 : Int))))
  ** (intArray.missing_i ( &( "prefix" ) ) left (0 : Int) (n_pre + 1) prefix_l)
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)

noncomputable def mergingStones_partial_solve_wit_9 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (best : Int) (interval_sum : Int) (split : Int) (right : Int) (left : Int) (len : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (split < right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : ((left + len) <= n_pre)) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left <= split)) (PreH14 : (split <= right)) (PreH15 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH16 : (2 <= interval_sum)) (PreH17 : (interval_sum <= 8000)) (PreH18 : ((0 : Int) <= best)) (PreH19 : (best <= 1000000)) (PreH20 : (StoneSplitProgress stones_l dp_l n_pre len left split best)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ (split < right) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) stones_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) stones_l) ” &&
  “ (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l))) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + len) <= n_pre) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left <= split) ” &&
  “ (split <= right) ” &&
  “ (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l))))) ” &&
  “ (2 <= interval_sum) ” &&
  “ (interval_sum <= 8000) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 1000000) ” &&
  “ (StoneSplitProgress stones_l dp_l n_pre len left split best) ”
  &&  (((( &( "dp" ) ) + (((left * n_pre) + split) * sizeof(INT)))) # Int |-> ((Znth (split) ((Znth left dp_l __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (( &( "dp" ) ) + ((left * n_pre) * sizeof(INT))) split (0 : Int) n_pre (Znth left dp_l __default__List_Z))
  ** (intArray2.missing_i ( &( "dp" ) ) left (0 : Int) n_pre n_pre dp_l)
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)

noncomputable def mergingStones_partial_solve_wit_10 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (prefix_l : (List Int)) (dp_l : (List (List Int))) (len : Int) (left : Int) (right : Int) (split : Int) (interval_sum : Int) (best : Int) (left_value : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH4 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH5 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH6 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : ((left + len) <= n_pre)) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split <= right)) (PreH14 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH15 : (2 <= interval_sum)) (PreH16 : (interval_sum <= 8000)) (PreH17 : ((0 : Int) <= best)) (PreH18 : (best <= 1000000)) (PreH19 : (StoneSplitProgress stones_l dp_l n_pre len left split best)) (PreH20 : (split < right)) (PreH21 : (left_value = (Znth split (Znth left dp_l __default__List_Z) (0 : Int)))) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) stones_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) stones_l) ” &&
  “ (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l))) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + len) <= n_pre) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left <= split) ” &&
  “ (split <= right) ” &&
  “ (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l))))) ” &&
  “ (2 <= interval_sum) ” &&
  “ (interval_sum <= 8000) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 1000000) ” &&
  “ (StoneSplitProgress stones_l dp_l n_pre len left split best) ” &&
  “ (split < right) ” &&
  “ (left_value = (Znth split (Znth left dp_l __default__List_Z) (0 : Int))) ”
  &&  (((( &( "dp" ) ) + ((((split + 1) * n_pre) + right) * sizeof(INT)))) # Int |-> ((Znth (right) ((Znth (split + 1) dp_l __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (( &( "dp" ) ) + (((split + 1) * n_pre) * sizeof(INT))) right (0 : Int) n_pre (Znth (split + 1) dp_l __default__List_Z))
  ** (intArray2.missing_i ( &( "dp" ) ) (split + 1) (0 : Int) n_pre n_pre dp_l)
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)

noncomputable def mergingStones_partial_solve_wit_11 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (best : Int) (interval_sum : Int) (split : Int) (right : Int) (left : Int) (len : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (split >= right)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : ((left + len) <= n_pre)) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left <= split)) (PreH14 : (split <= right)) (PreH15 : (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l)))))) (PreH16 : (2 <= interval_sum)) (PreH17 : (interval_sum <= 8000)) (PreH18 : ((0 : Int) <= best)) (PreH19 : (best <= 1000000)) (PreH20 : (StoneSplitProgress stones_l dp_l n_pre len left split best)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ (split >= right) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) stones_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) stones_l) ” &&
  “ (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l))) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + len) <= n_pre) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left <= split) ” &&
  “ (split <= right) ” &&
  “ (interval_sum = (sum ((sublist (left) ((right + 1)) (stones_l))))) ” &&
  “ (2 <= interval_sum) ” &&
  “ (interval_sum <= 8000) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 1000000) ” &&
  “ (StoneSplitProgress stones_l dp_l n_pre len left split best) ”
  &&  (((( &( "dp" ) ) + (((left * n_pre) + right) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i (( &( "dp" ) ) + ((left * n_pre) * sizeof(INT))) right (0 : Int) n_pre (Znth left dp_l __default__List_Z))
  ** (intArray2.missing_i ( &( "dp" ) ) left (0 : Int) n_pre n_pre dp_l)
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)

noncomputable def mergingStones_partial_solve_wit_12 : Prop :=
  forall (n_pre : Int) (stones_pre : Int) (stones_l : (List Int)) (len : Int) (prefix_l : (List Int)) (dp_l : (List (List Int))) (__default__List_Z : _List_Z) (PreH1 : (len > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) stones_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) stones_l)) (PreH6 : (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l)))) (PreH7 : (StonePrefixDone stones_l prefix_l n_pre)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1))) (PreH10 : (StoneLenDone stones_l dp_l n_pre len)) ,
  (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray2.full ( &( "dp" ) ) n_pre n_pre dp_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)
|--
  “ (len > n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) stones_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) stones_l) ” &&
  “ (Forall (Eq (n_pre)) (List.map (Zlength) (dp_l))) ” &&
  “ (StonePrefixDone stones_l prefix_l n_pre) ” &&
  “ (2 <= len) ” &&
  “ (len <= (n_pre + 1)) ” &&
  “ (StoneLenDone stones_l dp_l n_pre len) ”
  &&  (((( &( "dp" ) ) + ((((0 : Int) * n_pre) + (n_pre - 1)) * sizeof(INT)))) # Int |-> ((Znth ((n_pre - 1)) ((Znth (0 : Int) dp_l __default__List_Z)) ((0 : Int)))))
  ** (intArray.missing_i (( &( "dp" ) ) + (((0 : Int) * n_pre) * sizeof(INT))) (n_pre - 1) (0 : Int) n_pre (Znth (0 : Int) dp_l __default__List_Z))
  ** (intArray2.missing_i ( &( "dp" ) ) (0 : Int) (0 : Int) n_pre n_pre dp_l)
  ** (intArray.full stones_pre n_pre stones_l)
  ** (intArray.full ( &( "prefix" ) ) (n_pre + 1) prefix_l)
  ** (intArray.undef_seg ( &( "prefix" ) ) (n_pre + 1) 9)
  ** (intArray.undef_seg ( &( "dp" ) ) (n_pre * n_pre) 64)


structure VC_Correct : Type where
  proof_of_mergingStones_safety_wit_1 : mergingStones_safety_wit_1
  proof_of_mergingStones_safety_wit_2 : mergingStones_safety_wit_2
  proof_of_mergingStones_safety_wit_3 : mergingStones_safety_wit_3
  proof_of_mergingStones_safety_wit_4 : mergingStones_safety_wit_4
  proof_of_mergingStones_safety_wit_5 : mergingStones_safety_wit_5
  proof_of_mergingStones_safety_wit_6 : mergingStones_safety_wit_6
  proof_of_mergingStones_safety_wit_7 : mergingStones_safety_wit_7
  proof_of_mergingStones_safety_wit_8 : mergingStones_safety_wit_8
  proof_of_mergingStones_safety_wit_9 : mergingStones_safety_wit_9
  proof_of_mergingStones_safety_wit_11 : mergingStones_safety_wit_11
  proof_of_mergingStones_safety_wit_12 : mergingStones_safety_wit_12
  proof_of_mergingStones_safety_wit_13 : mergingStones_safety_wit_13
  proof_of_mergingStones_safety_wit_14 : mergingStones_safety_wit_14
  proof_of_mergingStones_safety_wit_15 : mergingStones_safety_wit_15
  proof_of_mergingStones_safety_wit_16 : mergingStones_safety_wit_16
  proof_of_mergingStones_safety_wit_17 : mergingStones_safety_wit_17
  proof_of_mergingStones_safety_wit_18 : mergingStones_safety_wit_18
  proof_of_mergingStones_safety_wit_19 : mergingStones_safety_wit_19
  proof_of_mergingStones_safety_wit_20 : mergingStones_safety_wit_20
  proof_of_mergingStones_safety_wit_21 : mergingStones_safety_wit_21
  proof_of_mergingStones_safety_wit_22 : mergingStones_safety_wit_22
  proof_of_mergingStones_safety_wit_23 : mergingStones_safety_wit_23
  proof_of_mergingStones_safety_wit_24 : mergingStones_safety_wit_24
  proof_of_mergingStones_safety_wit_26 : mergingStones_safety_wit_26
  proof_of_mergingStones_safety_wit_27 : mergingStones_safety_wit_27
  proof_of_mergingStones_safety_wit_28 : mergingStones_safety_wit_28
  proof_of_mergingStones_safety_wit_29 : mergingStones_safety_wit_29
  proof_of_mergingStones_safety_wit_30 : mergingStones_safety_wit_30
  proof_of_mergingStones_safety_wit_31 : mergingStones_safety_wit_31
  proof_of_mergingStones_safety_wit_32 : mergingStones_safety_wit_32
  proof_of_mergingStones_safety_wit_33 : mergingStones_safety_wit_33
  proof_of_mergingStones_safety_wit_34 : mergingStones_safety_wit_34
  proof_of_mergingStones_safety_wit_37 : mergingStones_safety_wit_37
  proof_of_mergingStones_safety_wit_38 : mergingStones_safety_wit_38
  proof_of_mergingStones_safety_wit_39 : mergingStones_safety_wit_39
  proof_of_mergingStones_safety_wit_40 : mergingStones_safety_wit_40
  proof_of_mergingStones_safety_wit_41 : mergingStones_safety_wit_41
  proof_of_mergingStones_safety_wit_42 : mergingStones_safety_wit_42
  proof_of_mergingStones_safety_wit_43 : mergingStones_safety_wit_43
  proof_of_mergingStones_safety_wit_44 : mergingStones_safety_wit_44
  proof_of_mergingStones_safety_wit_45 : mergingStones_safety_wit_45
  proof_of_mergingStones_safety_wit_46 : mergingStones_safety_wit_46
  proof_of_mergingStones_safety_wit_47 : mergingStones_safety_wit_47
  proof_of_mergingStones_entail_wit_1 : mergingStones_entail_wit_1
  proof_of_mergingStones_entail_wit_2 : mergingStones_entail_wit_2
  proof_of_mergingStones_return_wit_1 : mergingStones_return_wit_1
  proof_of_mergingStones_partial_solve_wit_1 : mergingStones_partial_solve_wit_1
  proof_of_mergingStones_partial_solve_wit_2 : mergingStones_partial_solve_wit_2
  proof_of_mergingStones_partial_solve_wit_3 : mergingStones_partial_solve_wit_3
  proof_of_mergingStones_partial_solve_wit_4 : mergingStones_partial_solve_wit_4
  proof_of_mergingStones_partial_solve_wit_5 : mergingStones_partial_solve_wit_5
  proof_of_mergingStones_partial_solve_wit_6 : mergingStones_partial_solve_wit_6
  proof_of_mergingStones_partial_solve_wit_7 : mergingStones_partial_solve_wit_7
  proof_of_mergingStones_partial_solve_wit_8 : mergingStones_partial_solve_wit_8
  proof_of_mergingStones_partial_solve_wit_9 : mergingStones_partial_solve_wit_9
  proof_of_mergingStones_partial_solve_wit_10 : mergingStones_partial_solve_wit_10
  proof_of_mergingStones_partial_solve_wit_11 : mergingStones_partial_solve_wit_11
  proof_of_mergingStones_partial_solve_wit_12 : mergingStones_partial_solve_wit_12
  proof_of_mergingStones_safety_wit_10 : mergingStones_safety_wit_10
  proof_of_mergingStones_safety_wit_25 : mergingStones_safety_wit_25
  proof_of_mergingStones_safety_wit_35 : mergingStones_safety_wit_35
  proof_of_mergingStones_safety_wit_36 : mergingStones_safety_wit_36
  proof_of_mergingStones_entail_wit_3 : mergingStones_entail_wit_3
  proof_of_mergingStones_entail_wit_4 : mergingStones_entail_wit_4
  proof_of_mergingStones_entail_wit_5 : mergingStones_entail_wit_5
  proof_of_mergingStones_entail_wit_6 : mergingStones_entail_wit_6
  proof_of_mergingStones_entail_wit_7 : mergingStones_entail_wit_7
  proof_of_mergingStones_entail_wit_8 : mergingStones_entail_wit_8
  proof_of_mergingStones_entail_wit_9 : mergingStones_entail_wit_9
  proof_of_mergingStones_entail_wit_10 : mergingStones_entail_wit_10
  proof_of_mergingStones_entail_wit_11 : mergingStones_entail_wit_11
  proof_of_mergingStones_entail_wit_12 : mergingStones_entail_wit_12
  proof_of_mergingStones_entail_wit_13_1 : mergingStones_entail_wit_13_1
  proof_of_mergingStones_entail_wit_13_2 : mergingStones_entail_wit_13_2
  proof_of_mergingStones_entail_wit_14 : mergingStones_entail_wit_14
  proof_of_mergingStones_entail_wit_15 : mergingStones_entail_wit_15
  proof_of_mergingStones_entail_wit_16 : mergingStones_entail_wit_16

end SimpleC.EE.LLM_bench.Algorithms.merging_stones.merging_stones_goal
