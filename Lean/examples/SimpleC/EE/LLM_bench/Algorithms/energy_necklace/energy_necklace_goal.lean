import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.energy_necklace.energy_necklace_lib
open SimpleC.EE.LLM_bench.Algorithms.energy_necklace.energy_necklace_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.energy_necklace.energy_necklace_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance energy_necklace_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def energyNecklace_safety_wit_1 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (PreH1 : (4 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (beads_l)) = n_pre)) (PreH4 : ((Zlength (beads_l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH6 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH7 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "total" ) )) # Int |->_)
  ** (intArray.undef_full ( &( "dp" ) ) 40000)
  ** (intArray.undef_full ( &( "vals" ) ) 200)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full beads_pre n_pre beads_l)
|--
  “ ((2 * n_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (2 * n_pre)) ”

noncomputable def energyNecklace_safety_wit_2 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (PreH1 : (4 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (beads_l)) = n_pre)) (PreH4 : ((Zlength (beads_l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH6 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH7 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "total" ) )) # Int |->_)
  ** (intArray.undef_full ( &( "dp" ) ) 40000)
  ** (intArray.undef_full ( &( "vals" ) ) 200)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full beads_pre n_pre beads_l)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def energyNecklace_safety_wit_3 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (PreH1 : (4 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (beads_l)) = n_pre)) (PreH4 : ((Zlength (beads_l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH6 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH7 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "width" ) )) # Int |-> ((2 * n_pre)))
  ** ((( &( "total" ) )) # Int |-> ((2 * n_pre)))
  ** (intArray.undef_full ( &( "dp" ) ) 40000)
  ** (intArray.undef_full ( &( "vals" ) ) 200)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full beads_pre n_pre beads_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def energyNecklace_safety_wit_4 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (i : Int) (vals_l : (List Int)) (width : Int) (total : Int) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 Eq (sublist ((0 : Int)) (i) (vals_l)) (sublist ((0 : Int)) (i) (beads_l)))) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH15 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH16 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  (intArray.seg ( &( "vals" ) ) (0 : Int) (i + 1) (vals_l ++ ((Znth i beads_l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "vals" ) ) (i + 1) total)
  ** (intArray.full beads_pre n_pre beads_l)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_full ( &( "dp" ) ) (total * width))
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def energyNecklace_safety_wit_5 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (i : Int) (vals_l : (List Int)) (width : Int) (total : Int) (PreH1 : (i >= n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 Eq (sublist ((0 : Int)) (i) (vals_l)) (sublist ((0 : Int)) (i) (beads_l)))) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH15 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH16 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.seg ( &( "vals" ) ) (0 : Int) i vals_l)
  ** (intArray.undef_seg ( &( "vals" ) ) i total)
  ** (intArray.undef_full ( &( "dp" ) ) (total * width))
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def energyNecklace_safety_wit_6 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (i : Int) (vals_l : (List Int)) (width : Int) (total : Int) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l)) = (n_pre + i))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 Eq (sublist ((0 : Int)) (n_pre) (vals_l)) (sublist ((0 : Int)) (n_pre) (beads_l)))) (PreH13 : (Forall2 Eq (sublist (n_pre) ((n_pre + i)) (vals_l)) (sublist ((0 : Int)) (i) (beads_l)))) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH16 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH17 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.seg ( &( "vals" ) ) (0 : Int) (n_pre + i) vals_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (n_pre + i) total)
  ** (intArray.undef_full ( &( "dp" ) ) (total * width))
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ ((n_pre + i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre + i)) ”

noncomputable def energyNecklace_safety_wit_7 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (i : Int) (vals_l : (List Int)) (width : Int) (total : Int) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l)) = (n_pre + i))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 Eq (sublist ((0 : Int)) (n_pre) (vals_l)) (sublist ((0 : Int)) (n_pre) (beads_l)))) (PreH13 : (Forall2 Eq (sublist (n_pre) ((n_pre + i)) (vals_l)) (sublist ((0 : Int)) (i) (beads_l)))) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH16 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH17 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  (intArray.seg ( &( "vals" ) ) (0 : Int) ((n_pre + i) + 1) (vals_l ++ ((Znth i beads_l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "vals" ) ) ((n_pre + i) + 1) total)
  ** (intArray.full beads_pre n_pre beads_l)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_full ( &( "dp" ) ) (total * width))
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def energyNecklace_safety_wit_8 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (i : Int) (vals_l : (List Int)) (width : Int) (total : Int) (PreH1 : (i >= n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l)) = (n_pre + i))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 Eq (sublist ((0 : Int)) (n_pre) (vals_l)) (sublist ((0 : Int)) (n_pre) (beads_l)))) (PreH13 : (Forall2 Eq (sublist (n_pre) ((n_pre + i)) (vals_l)) (sublist ((0 : Int)) (i) (beads_l)))) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH16 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH17 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.seg ( &( "vals" ) ) (0 : Int) (n_pre + i) vals_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (n_pre + i) total)
  ** (intArray.undef_full ( &( "dp" ) ) (total * width))
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def energyNecklace_safety_wit_9 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (i : Int) (dp_l : (List Int)) (width : Int) (total : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : ((Zlength (dp_l)) = i)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= (total * width))) (PreH11 : (Forall (Eq ((0 : Int))) dp_l)) (PreH12 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH15 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH16 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) i dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) i (total * width))
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ ((total * width) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (total * width)) ”

noncomputable def energyNecklace_safety_wit_10 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (i : Int) (dp_l : (List Int)) (width : Int) (total : Int) (PreH1 : (i < (total * width))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (total * width))) (PreH12 : (Forall (Eq ((0 : Int))) dp_l)) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH16 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH17 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) i dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) i (total * width))
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def energyNecklace_safety_wit_11 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (i : Int) (dp_l : (List Int)) (width : Int) (total : Int) (PreH1 : (i < (total * width))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (total * width))) (PreH12 : (Forall (Eq ((0 : Int))) dp_l)) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH16 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH17 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  (intArray.seg ( &( "dp" ) ) (0 : Int) (i + 1) (dp_l ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "dp" ) ) (i + 1) (total * width))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def energyNecklace_safety_wit_12 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (i : Int) (dp_l : (List Int)) (width : Int) (total : Int) (PreH1 : (i >= (total * width))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (total * width))) (PreH12 : (Forall (Eq ((0 : Int))) dp_l)) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH16 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH17 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "len" ) )) # Int |->_)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) i dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) i (total * width))
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def energyNecklace_safety_wit_13 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (len : Int) (width : Int) (total : Int) (PreH1 : (len <= n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l)) = (total * width))) (PreH12 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (width = total)) (PreH15 : ((Zlength (vals_l)) = total)) (PreH16 : ((Zlength (dp_l)) = (total * width))) (PreH17 : (1 <= len)) (PreH18 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH19 : ((Zlength (beads_l)) = n_pre)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH22 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "left" ) )) # Int |->_)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def energyNecklace_safety_wit_14 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left <= (total - len))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width))) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH14 : ((0 : Int) <= total)) (PreH15 : (width = total)) (PreH16 : ((Zlength (vals_l)) = total)) (PreH17 : ((Zlength (dp_l)) = (total * width))) (PreH18 : (1 <= len)) (PreH19 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH20 : (2 <= len)) (PreH21 : ((0 : Int) <= left)) (PreH22 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH23 : ((Zlength (beads_l)) = n_pre)) (PreH24 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH25 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH26 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ ((total - len) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (total - len)) ”

noncomputable def energyNecklace_safety_wit_15 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (left < (total - len))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= (total - len))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l)) = total)) (PreH18 : ((Zlength (dp_l)) = (total * width))) (PreH19 : (1 <= len)) (PreH20 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH21 : (2 <= len)) (PreH22 : ((0 : Int) <= left)) (PreH23 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH26 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH27 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "right" ) )) # Int |->_)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ (((left + len) - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((left + len) - 1)) ”

noncomputable def energyNecklace_safety_wit_16 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (left < (total - len))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= (total - len))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l)) = total)) (PreH18 : ((Zlength (dp_l)) = (total * width))) (PreH19 : (1 <= len)) (PreH20 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH21 : (2 <= len)) (PreH22 : ((0 : Int) <= left)) (PreH23 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH26 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH27 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "right" ) )) # Int |->_)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ ((left + len) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left + len)) ”

noncomputable def energyNecklace_safety_wit_17 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (left < (total - len))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= (total - len))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l)) = total)) (PreH18 : ((Zlength (dp_l)) = (total * width))) (PreH19 : (1 <= len)) (PreH20 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH21 : (2 <= len)) (PreH22 : ((0 : Int) <= left)) (PreH23 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH26 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH27 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "right" ) )) # Int |->_)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def energyNecklace_safety_wit_18 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (left < (total - len))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= (total - len))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l)) = total)) (PreH18 : ((Zlength (dp_l)) = (total * width))) (PreH19 : (1 <= len)) (PreH20 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH21 : (2 <= len)) (PreH22 : ((0 : Int) <= left)) (PreH23 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH26 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH27 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "best" ) )) # Int |->_)
  ** ((( &( "right" ) )) # Int |-> (((left + len) - 1)))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def energyNecklace_safety_wit_19 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : ((0 : Int) <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH36 : (2 <= len)) (PreH37 : ((0 : Int) <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH39 : ((left + len) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len) - 1))) (PreH42 : ((0 : Int) <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best)) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH48 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "left_value" ) )) # Int |->_)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ (((left * width) + split) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((left * width) + split)) ”

noncomputable def energyNecklace_safety_wit_20 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : ((0 : Int) <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH36 : (2 <= len)) (PreH37 : ((0 : Int) <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH39 : ((left + len) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len) - 1))) (PreH42 : ((0 : Int) <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best)) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH48 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "left_value" ) )) # Int |->_)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ ((left * width) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left * width)) ”

noncomputable def energyNecklace_safety_wit_21 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : ((0 : Int) <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH36 : (2 <= len)) (PreH37 : ((0 : Int) <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH39 : ((left + len) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len) - 1))) (PreH42 : ((0 : Int) <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best)) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH48 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "right_value" ) )) # Int |->_)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ ((((split + 1) * width) + right) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((split + 1) * width) + right)) ”

noncomputable def energyNecklace_safety_wit_22 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : ((0 : Int) <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH36 : (2 <= len)) (PreH37 : ((0 : Int) <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH39 : ((left + len) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len) - 1))) (PreH42 : ((0 : Int) <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best)) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH48 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "right_value" ) )) # Int |->_)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ (((split + 1) * width) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((split + 1) * width)) ”

noncomputable def energyNecklace_safety_wit_23 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : ((0 : Int) <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH36 : (2 <= len)) (PreH37 : ((0 : Int) <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH39 : ((left + len) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len) - 1))) (PreH42 : ((0 : Int) <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best)) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH48 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "right_value" ) )) # Int |->_)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ ((split + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (split + 1)) ”

noncomputable def energyNecklace_safety_wit_24 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : ((0 : Int) <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH36 : (2 <= len)) (PreH37 : ((0 : Int) <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH39 : ((left + len) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len) - 1))) (PreH42 : ((0 : Int) <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best)) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH48 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "right_value" ) )) # Int |->_)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def energyNecklace_safety_wit_25 : Prop :=
  (
forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : ((0 : Int) <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH36 : (2 <= len)) (PreH37 : ((0 : Int) <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH39 : ((left + len) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len) - 1))) (PreH42 : ((0 : Int) <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best)) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH48 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  (intArray.full ( &( "vals" ) ) total vals_l)
  ** ((( &( "gain" ) )) # Int |->_)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ ((((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int)))) ”
) \/
(
forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : ((0 : Int) <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH36 : (2 <= len)) (PreH37 : ((0 : Int) <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH39 : ((left + len) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len) - 1))) (PreH42 : ((0 : Int) <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best)) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH48 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  (intArray.full ( &( "vals" ) ) total vals_l)
  ** ((( &( "gain" ) )) # Int |->_)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ ((((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int)))) ”
)

noncomputable def energyNecklace_safety_wit_25_split_goal_1 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : ((0 : Int) <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH36 : (2 <= len)) (PreH37 : ((0 : Int) <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH39 : ((left + len) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len) - 1))) (PreH42 : ((0 : Int) <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best)) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH48 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  (intArray.full ( &( "vals" ) ) total vals_l)
  ** ((( &( "gain" ) )) # Int |->_)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ ((((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int))) <= INT_MAX) ”

noncomputable def energyNecklace_safety_wit_25_split_goal_2 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : ((0 : Int) <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH36 : (2 <= len)) (PreH37 : ((0 : Int) <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH39 : ((left + len) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len) - 1))) (PreH42 : ((0 : Int) <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best)) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH48 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  (intArray.full ( &( "vals" ) ) total vals_l)
  ** ((( &( "gain" ) )) # Int |->_)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ ((INT_MIN) <= (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int)))) ”

noncomputable def energyNecklace_safety_wit_26 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : ((0 : Int) <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH36 : (2 <= len)) (PreH37 : ((0 : Int) <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH39 : ((left + len) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len) - 1))) (PreH42 : ((0 : Int) <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best)) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH48 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  (intArray.full ( &( "vals" ) ) total vals_l)
  ** ((( &( "gain" ) )) # Int |->_)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ ((right + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (right + 1)) ”

noncomputable def energyNecklace_safety_wit_27 : Prop :=
  (
forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : ((0 : Int) <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH36 : (2 <= len)) (PreH37 : ((0 : Int) <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH39 : ((left + len) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len) - 1))) (PreH42 : ((0 : Int) <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best)) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH48 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  (intArray.full ( &( "vals" ) ) total vals_l)
  ** ((( &( "gain" ) )) # Int |->_)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int)))) ”
) \/
(
forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : ((0 : Int) <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH36 : (2 <= len)) (PreH37 : ((0 : Int) <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH39 : ((left + len) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len) - 1))) (PreH42 : ((0 : Int) <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best)) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH48 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  (intArray.full ( &( "vals" ) ) total vals_l)
  ** ((( &( "gain" ) )) # Int |->_)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int)))) ”
)

noncomputable def energyNecklace_safety_wit_27_split_goal_1 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : ((0 : Int) <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH36 : (2 <= len)) (PreH37 : ((0 : Int) <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH39 : ((left + len) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len) - 1))) (PreH42 : ((0 : Int) <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best)) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH48 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  (intArray.full ( &( "vals" ) ) total vals_l)
  ** ((( &( "gain" ) )) # Int |->_)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) <= INT_MAX) ”

noncomputable def energyNecklace_safety_wit_27_split_goal_2 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : ((0 : Int) <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH36 : (2 <= len)) (PreH37 : ((0 : Int) <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH39 : ((left + len) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len) - 1))) (PreH42 : ((0 : Int) <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best)) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH48 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  (intArray.full ( &( "vals" ) ) total vals_l)
  ** ((( &( "gain" ) )) # Int |->_)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ ((INT_MIN) <= ((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int)))) ”

noncomputable def energyNecklace_safety_wit_28 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : ((0 : Int) <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH36 : (2 <= len)) (PreH37 : ((0 : Int) <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH39 : ((left + len) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len) - 1))) (PreH42 : ((0 : Int) <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best)) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH48 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  (intArray.full ( &( "vals" ) ) total vals_l)
  ** ((( &( "gain" ) )) # Int |->_)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ ((split + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (split + 1)) ”

noncomputable def energyNecklace_safety_wit_29 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : ((0 : Int) <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH36 : (2 <= len)) (PreH37 : ((0 : Int) <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH39 : ((left + len) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len) - 1))) (PreH42 : ((0 : Int) <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best)) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH48 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  (intArray.full ( &( "vals" ) ) total vals_l)
  ** ((( &( "gain" ) )) # Int |->_)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def energyNecklace_safety_wit_30 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : ((0 : Int) <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH36 : (2 <= len)) (PreH37 : ((0 : Int) <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH39 : ((left + len) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len) - 1))) (PreH42 : ((0 : Int) <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best)) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH48 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  (intArray.full ( &( "vals" ) ) total vals_l)
  ** ((( &( "gain" ) )) # Int |->_)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def energyNecklace_safety_wit_31 : Prop :=
  (
forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : ((0 : Int) <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH36 : (2 <= len)) (PreH37 : ((0 : Int) <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH39 : ((left + len) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len) - 1))) (PreH42 : ((0 : Int) <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best)) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH48 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "candidate" ) )) # Int |->_)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** ((( &( "gain" ) )) # Int |-> ((((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int)))))
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ ((((Znth ((left * width) + split) dp_l (0 : Int)) + (Znth (((split + 1) * width) + right) dp_l (0 : Int))) + (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int)))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((Znth ((left * width) + split) dp_l (0 : Int)) + (Znth (((split + 1) * width) + right) dp_l (0 : Int))) + (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int))))) ”
) \/
(
forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : ((0 : Int) <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH36 : (2 <= len)) (PreH37 : ((0 : Int) <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH39 : ((left + len) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len) - 1))) (PreH42 : ((0 : Int) <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best)) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH48 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "candidate" ) )) # Int |->_)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** ((( &( "gain" ) )) # Int |-> ((((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int)))))
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ ((((Znth ((left * width) + split) dp_l (0 : Int)) + (Znth (((split + 1) * width) + right) dp_l (0 : Int))) + (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int)))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((Znth ((left * width) + split) dp_l (0 : Int)) + (Znth (((split + 1) * width) + right) dp_l (0 : Int))) + (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int))))) ”
)

noncomputable def energyNecklace_safety_wit_31_split_goal_1 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : ((0 : Int) <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH36 : (2 <= len)) (PreH37 : ((0 : Int) <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH39 : ((left + len) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len) - 1))) (PreH42 : ((0 : Int) <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best)) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH48 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "candidate" ) )) # Int |->_)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** ((( &( "gain" ) )) # Int |-> ((((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int)))))
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ ((((Znth ((left * width) + split) dp_l (0 : Int)) + (Znth (((split + 1) * width) + right) dp_l (0 : Int))) + (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int)))) <= INT_MAX) ”

noncomputable def energyNecklace_safety_wit_31_split_goal_2 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : ((0 : Int) <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH36 : (2 <= len)) (PreH37 : ((0 : Int) <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH39 : ((left + len) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len) - 1))) (PreH42 : ((0 : Int) <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best)) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH48 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "candidate" ) )) # Int |->_)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** ((( &( "gain" ) )) # Int |-> ((((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int)))))
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ ((INT_MIN) <= (((Znth ((left * width) + split) dp_l (0 : Int)) + (Znth (((split + 1) * width) + right) dp_l (0 : Int))) + (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int))))) ”

noncomputable def energyNecklace_safety_wit_32 : Prop :=
  (
forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : ((0 : Int) <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH36 : (2 <= len)) (PreH37 : ((0 : Int) <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH39 : ((left + len) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len) - 1))) (PreH42 : ((0 : Int) <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best)) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH48 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "candidate" ) )) # Int |->_)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** ((( &( "gain" ) )) # Int |-> ((((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int)))))
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ (((Znth ((left * width) + split) dp_l (0 : Int)) + (Znth (((split + 1) * width) + right) dp_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth ((left * width) + split) dp_l (0 : Int)) + (Znth (((split + 1) * width) + right) dp_l (0 : Int)))) ”
) \/
(
forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : ((0 : Int) <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH36 : (2 <= len)) (PreH37 : ((0 : Int) <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH39 : ((left + len) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len) - 1))) (PreH42 : ((0 : Int) <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best)) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH48 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "candidate" ) )) # Int |->_)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** ((( &( "gain" ) )) # Int |-> ((((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int)))))
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ (((Znth ((left * width) + split) dp_l (0 : Int)) + (Znth (((split + 1) * width) + right) dp_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth ((left * width) + split) dp_l (0 : Int)) + (Znth (((split + 1) * width) + right) dp_l (0 : Int)))) ”
)

noncomputable def energyNecklace_safety_wit_32_split_goal_1 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : ((0 : Int) <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH36 : (2 <= len)) (PreH37 : ((0 : Int) <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH39 : ((left + len) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len) - 1))) (PreH42 : ((0 : Int) <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best)) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH48 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "candidate" ) )) # Int |->_)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** ((( &( "gain" ) )) # Int |-> ((((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int)))))
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ (((Znth ((left * width) + split) dp_l (0 : Int)) + (Znth (((split + 1) * width) + right) dp_l (0 : Int))) <= INT_MAX) ”

noncomputable def energyNecklace_safety_wit_32_split_goal_2 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : ((0 : Int) <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH36 : (2 <= len)) (PreH37 : ((0 : Int) <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH39 : ((left + len) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len) - 1))) (PreH42 : ((0 : Int) <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best)) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH48 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "candidate" ) )) # Int |->_)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** ((( &( "gain" ) )) # Int |-> ((((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int)))))
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** ((( &( "right_value" ) )) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** ((( &( "left_value" ) )) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ ((INT_MIN) <= ((Znth ((left * width) + split) dp_l (0 : Int)) + (Znth (((split + 1) * width) + right) dp_l (0 : Int)))) ”

noncomputable def energyNecklace_safety_wit_33 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (right_value : Int) (gain : Int) (candidate : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((right + 1) < total)) (PreH15 : (left_value = (Znth ((left * width) + split) dp_l (0 : Int)))) (PreH16 : (right_value = (Znth (((split + 1) * width) + right) dp_l (0 : Int)))) (PreH17 : (gain = (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int))))) (PreH18 : (candidate = ((left_value + right_value) + gain))) (PreH19 : ((0 : Int) <= candidate)) (PreH20 : (candidate <= 2100000000)) (PreH21 : ((0 : Int) <= best)) (PreH22 : (best <= 2100000000)) (PreH23 : ((Zlength (beads_l)) = n_pre)) (PreH24 : ((Zlength (dp_l)) = (total * width))) (PreH25 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH26 : ((0 : Int) <= total)) (PreH27 : (width = total)) (PreH28 : ((Zlength (vals_l)) = total)) (PreH29 : ((Zlength (dp_l)) = (total * width))) (PreH30 : (1 <= len)) (PreH31 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH32 : (2 <= len)) (PreH33 : ((0 : Int) <= left)) (PreH34 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH35 : ((left + len) <= total)) (PreH36 : (left <= (split + 1))) (PreH37 : ((split + 1) <= ((left + len) - 1))) (PreH38 : ((0 : Int) <= best)) (PreH39 : (best <= 2100000000)) (PreH40 : (EnergySplitBest vals_l dp_l width len left (split + 1) best)) (PreH41 : ((Zlength (beads_l)) = n_pre)) (PreH42 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH44 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ ((split + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (split + 1)) ”

noncomputable def energyNecklace_safety_wit_34 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : ((right + 1) < total)) (PreH13 : ((0 : Int) <= ((left * width) + right))) (PreH14 : (((left * width) + right) < (total * width))) (PreH15 : ((0 : Int) <= best)) (PreH16 : (best <= 2100000000)) (PreH17 : ((Zlength (beads_l)) = n_pre)) (PreH18 : ((Zlength (dp_l)) = (total * width))) (PreH19 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (width = total)) (PreH22 : ((Zlength (vals_l)) = total)) (PreH23 : ((Zlength (dp_l)) = (total * width))) (PreH24 : (1 <= len)) (PreH25 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH26 : (2 <= len)) (PreH27 : ((0 : Int) <= left)) (PreH28 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH29 : ((left + len) <= total)) (PreH30 : (left <= right)) (PreH31 : (right <= ((left + len) - 1))) (PreH32 : ((0 : Int) <= best)) (PreH33 : (best <= 2100000000)) (PreH34 : (EnergySplitBest vals_l dp_l width len left right best)) (PreH35 : (EnergyIntervalBest vals_l left right best)) (PreH36 : ((Zlength (beads_l)) = n_pre)) (PreH37 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH39 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ (((left * width) + right) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((left * width) + right)) ”

noncomputable def energyNecklace_safety_wit_35 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : ((right + 1) < total)) (PreH13 : ((0 : Int) <= ((left * width) + right))) (PreH14 : (((left * width) + right) < (total * width))) (PreH15 : ((0 : Int) <= best)) (PreH16 : (best <= 2100000000)) (PreH17 : ((Zlength (beads_l)) = n_pre)) (PreH18 : ((Zlength (dp_l)) = (total * width))) (PreH19 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (width = total)) (PreH22 : ((Zlength (vals_l)) = total)) (PreH23 : ((Zlength (dp_l)) = (total * width))) (PreH24 : (1 <= len)) (PreH25 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH26 : (2 <= len)) (PreH27 : ((0 : Int) <= left)) (PreH28 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH29 : ((left + len) <= total)) (PreH30 : (left <= right)) (PreH31 : (right <= ((left + len) - 1))) (PreH32 : ((0 : Int) <= best)) (PreH33 : (best <= 2100000000)) (PreH34 : (EnergySplitBest vals_l dp_l width len left right best)) (PreH35 : (EnergyIntervalBest vals_l left right best)) (PreH36 : ((Zlength (beads_l)) = n_pre)) (PreH37 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH39 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ ((left * width) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left * width)) ”

noncomputable def energyNecklace_safety_wit_36 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : ((right + 1) < total)) (PreH13 : ((0 : Int) <= ((left * width) + right))) (PreH14 : (((left * width) + right) < (total * width))) (PreH15 : ((0 : Int) <= best)) (PreH16 : (best <= 2100000000)) (PreH17 : ((Zlength (beads_l)) = n_pre)) (PreH18 : ((Zlength (dp_l)) = (total * width))) (PreH19 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (width = total)) (PreH22 : ((Zlength (vals_l)) = total)) (PreH23 : ((Zlength (dp_l)) = (total * width))) (PreH24 : (1 <= len)) (PreH25 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH26 : (2 <= len)) (PreH27 : ((0 : Int) <= left)) (PreH28 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH29 : ((left + len) <= total)) (PreH30 : (left <= right)) (PreH31 : (right <= ((left + len) - 1))) (PreH32 : ((0 : Int) <= best)) (PreH33 : (best <= 2100000000)) (PreH34 : (EnergySplitBest vals_l dp_l width len left right best)) (PreH35 : (EnergyIntervalBest vals_l left right best)) (PreH36 : ((Zlength (beads_l)) = n_pre)) (PreH37 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH39 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  (intArray.full ( &( "dp" ) ) (total * width) (replace_Znth (((left * width) + right)) (best) (dp_l)))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ ((left + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left + 1)) ”

noncomputable def energyNecklace_safety_wit_37 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (left >= (total - len))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= (total - len))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l)) = total)) (PreH18 : ((Zlength (dp_l)) = (total * width))) (PreH19 : (1 <= len)) (PreH20 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH21 : (2 <= len)) (PreH22 : ((0 : Int) <= left)) (PreH23 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH26 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH27 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "len" ) )) # Int |-> (len))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ ((len + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (len + 1)) ”

noncomputable def energyNecklace_safety_wit_38 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (len : Int) (width : Int) (total : Int) (PreH1 : (len > n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l)) = (total * width))) (PreH12 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (width = total)) (PreH15 : ((Zlength (vals_l)) = total)) (PreH16 : ((Zlength (dp_l)) = (total * width))) (PreH17 : (1 <= len)) (PreH18 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH19 : ((Zlength (beads_l)) = n_pre)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH22 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "answer" ) )) # Int |->_)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def energyNecklace_safety_wit_39 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (len : Int) (width : Int) (total : Int) (PreH1 : (len > n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l)) = (total * width))) (PreH12 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (width = total)) (PreH15 : ((Zlength (vals_l)) = total)) (PreH16 : ((Zlength (dp_l)) = (total * width))) (PreH17 : (1 <= len)) (PreH18 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH19 : ((Zlength (beads_l)) = n_pre)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH22 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "start" ) )) # Int |->_)
  ** ((( &( "answer" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def energyNecklace_safety_wit_40 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (start : Int) (answer : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start < n_pre)) (PreH9 : ((0 : Int) <= ((((start * width) + start) + n_pre) - 1))) (PreH10 : (((((start * width) + start) + n_pre) - 1) < (total * width))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width))) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH14 : ((0 : Int) <= total)) (PreH15 : (width = total)) (PreH16 : ((Zlength (vals_l)) = total)) (PreH17 : ((Zlength (dp_l)) = (total * width))) (PreH18 : (1 <= (n_pre + 1))) (PreH19 : (EnergyLengthsComplete vals_l dp_l width (n_pre + 1))) (PreH20 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH21 : ((Zlength (dp_l)) = (total * width))) (PreH22 : (width = total)) (PreH23 : ((0 : Int) <= start)) (PreH24 : (start <= n_pre)) (PreH25 : ((0 : Int) <= answer)) (PreH26 : (answer <= 2100000000)) (PreH27 : (EnergyAnswerBest vals_l n_pre start answer)) (PreH28 : (EnergyIntervalBest vals_l start ((start + n_pre) - 1) (Znth ((((start * width) + start) + n_pre) - 1) dp_l (0 : Int)))) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH31 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH32 : forall (ev : (List Int)) , forall (start_2 : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev start_2 ((start_2 + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "value" ) )) # Int |->_)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ (((((start * width) + start) + n_pre) - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((((start * width) + start) + n_pre) - 1)) ”

noncomputable def energyNecklace_safety_wit_41 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (start : Int) (answer : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start < n_pre)) (PreH9 : ((0 : Int) <= ((((start * width) + start) + n_pre) - 1))) (PreH10 : (((((start * width) + start) + n_pre) - 1) < (total * width))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width))) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH14 : ((0 : Int) <= total)) (PreH15 : (width = total)) (PreH16 : ((Zlength (vals_l)) = total)) (PreH17 : ((Zlength (dp_l)) = (total * width))) (PreH18 : (1 <= (n_pre + 1))) (PreH19 : (EnergyLengthsComplete vals_l dp_l width (n_pre + 1))) (PreH20 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH21 : ((Zlength (dp_l)) = (total * width))) (PreH22 : (width = total)) (PreH23 : ((0 : Int) <= start)) (PreH24 : (start <= n_pre)) (PreH25 : ((0 : Int) <= answer)) (PreH26 : (answer <= 2100000000)) (PreH27 : (EnergyAnswerBest vals_l n_pre start answer)) (PreH28 : (EnergyIntervalBest vals_l start ((start + n_pre) - 1) (Znth ((((start * width) + start) + n_pre) - 1) dp_l (0 : Int)))) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH31 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH32 : forall (ev : (List Int)) , forall (start_2 : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev start_2 ((start_2 + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "value" ) )) # Int |->_)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ ((((start * width) + start) + n_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((start * width) + start) + n_pre)) ”

noncomputable def energyNecklace_safety_wit_42 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (start : Int) (answer : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start < n_pre)) (PreH9 : ((0 : Int) <= ((((start * width) + start) + n_pre) - 1))) (PreH10 : (((((start * width) + start) + n_pre) - 1) < (total * width))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width))) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH14 : ((0 : Int) <= total)) (PreH15 : (width = total)) (PreH16 : ((Zlength (vals_l)) = total)) (PreH17 : ((Zlength (dp_l)) = (total * width))) (PreH18 : (1 <= (n_pre + 1))) (PreH19 : (EnergyLengthsComplete vals_l dp_l width (n_pre + 1))) (PreH20 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH21 : ((Zlength (dp_l)) = (total * width))) (PreH22 : (width = total)) (PreH23 : ((0 : Int) <= start)) (PreH24 : (start <= n_pre)) (PreH25 : ((0 : Int) <= answer)) (PreH26 : (answer <= 2100000000)) (PreH27 : (EnergyAnswerBest vals_l n_pre start answer)) (PreH28 : (EnergyIntervalBest vals_l start ((start + n_pre) - 1) (Znth ((((start * width) + start) + n_pre) - 1) dp_l (0 : Int)))) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH31 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH32 : forall (ev : (List Int)) , forall (start_2 : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev start_2 ((start_2 + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "value" ) )) # Int |->_)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ (((start * width) + start) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((start * width) + start)) ”

noncomputable def energyNecklace_safety_wit_43 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (start : Int) (answer : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start < n_pre)) (PreH9 : ((0 : Int) <= ((((start * width) + start) + n_pre) - 1))) (PreH10 : (((((start * width) + start) + n_pre) - 1) < (total * width))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width))) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH14 : ((0 : Int) <= total)) (PreH15 : (width = total)) (PreH16 : ((Zlength (vals_l)) = total)) (PreH17 : ((Zlength (dp_l)) = (total * width))) (PreH18 : (1 <= (n_pre + 1))) (PreH19 : (EnergyLengthsComplete vals_l dp_l width (n_pre + 1))) (PreH20 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH21 : ((Zlength (dp_l)) = (total * width))) (PreH22 : (width = total)) (PreH23 : ((0 : Int) <= start)) (PreH24 : (start <= n_pre)) (PreH25 : ((0 : Int) <= answer)) (PreH26 : (answer <= 2100000000)) (PreH27 : (EnergyAnswerBest vals_l n_pre start answer)) (PreH28 : (EnergyIntervalBest vals_l start ((start + n_pre) - 1) (Znth ((((start * width) + start) + n_pre) - 1) dp_l (0 : Int)))) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH31 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH32 : forall (ev : (List Int)) , forall (start_2 : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev start_2 ((start_2 + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "value" ) )) # Int |->_)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ ((start * width) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (start * width)) ”

noncomputable def energyNecklace_safety_wit_44 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (start_2 : Int) (answer : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((0 : Int) <= start_2)) (PreH8 : (start_2 < n_pre)) (PreH9 : ((0 : Int) <= ((((start_2 * width) + start_2) + n_pre) - 1))) (PreH10 : (((((start_2 * width) + start_2) + n_pre) - 1) < (total * width))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width))) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH14 : ((0 : Int) <= total)) (PreH15 : (width = total)) (PreH16 : ((Zlength (vals_l)) = total)) (PreH17 : ((Zlength (dp_l)) = (total * width))) (PreH18 : (1 <= (n_pre + 1))) (PreH19 : (EnergyLengthsComplete vals_l dp_l width (n_pre + 1))) (PreH20 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH21 : ((Zlength (dp_l)) = (total * width))) (PreH22 : (width = total)) (PreH23 : ((0 : Int) <= start_2)) (PreH24 : (start_2 <= n_pre)) (PreH25 : ((0 : Int) <= answer)) (PreH26 : (answer <= 2100000000)) (PreH27 : (EnergyAnswerBest vals_l n_pre start_2 answer)) (PreH28 : (EnergyIntervalBest vals_l start_2 ((start_2 + n_pre) - 1) (Znth ((((start_2 * width) + start_2) + n_pre) - 1) dp_l (0 : Int)))) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH31 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH32 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "value" ) )) # Int |->_)
  ** ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "start" ) )) # Int |-> (start_2))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def energyNecklace_safety_wit_45 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (start : Int) (value : Int) (answer : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start < n_pre)) (PreH9 : (value = (Znth ((((start * width) + start) + n_pre) - 1) dp_l (0 : Int)))) (PreH10 : ((0 : Int) <= value)) (PreH11 : (value <= 2100000000)) (PreH12 : ((0 : Int) <= answer)) (PreH13 : (answer <= 2100000000)) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : ((Zlength (dp_l)) = (total * width))) (PreH16 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH17 : ((0 : Int) <= total)) (PreH18 : (width = total)) (PreH19 : ((Zlength (vals_l)) = total)) (PreH20 : ((Zlength (dp_l)) = (total * width))) (PreH21 : (1 <= (n_pre + 1))) (PreH22 : (EnergyLengthsComplete vals_l dp_l width (n_pre + 1))) (PreH23 : (EnergyIntervalBest vals_l start ((start + n_pre) - 1) value)) (PreH24 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH25 : ((Zlength (dp_l)) = (total * width))) (PreH26 : (width = total)) (PreH27 : ((0 : Int) <= (start + 1))) (PreH28 : ((start + 1) <= n_pre)) (PreH29 : ((0 : Int) <= answer)) (PreH30 : (answer <= 2100000000)) (PreH31 : (EnergyAnswerBest vals_l n_pre (start + 1) answer)) (PreH32 : ((Zlength (beads_l)) = n_pre)) (PreH33 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH34 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH35 : forall (ev : (List Int)) , forall (start_2 : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev start_2 ((start_2 + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "beads" ) )) # Ptr |-> (beads_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ ((start + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (start + 1)) ”

noncomputable def energyNecklace_entail_wit_1 : Prop :=
  (
forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (PreH1 : (4 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (beads_l)) = n_pre)) (PreH4 : ((Zlength (beads_l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH6 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH7 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (intArray.undef_full ( &( "dp" ) ) 40000)
  ** (intArray.undef_full ( &( "vals" ) ) 200)
  ** (intArray.full beads_pre n_pre beads_l)
|--
  EX vals_l : (List Int),
  “ ((2 * n_pre) = (2 * n_pre)) ” &&
  “ ((2 * n_pre) = (2 * n_pre)) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= (2 * n_pre)) ” &&
  “ ((2 * n_pre) <= 200) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (vals_l)) = (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (Forall2 Eq (sublist ((0 : Int)) ((0 : Int)) (vals_l)) (sublist ((0 : Int)) ((0 : Int)) (beads_l))) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) beads_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) beads_l) ” &&
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.seg ( &( "vals" ) ) (0 : Int) (0 : Int) vals_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (0 : Int) (2 * n_pre))
  ** (intArray.undef_full ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)))
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
) \/
(
forall (beads_l : (List Int)) (n_pre : Int) (PreH1 : (4 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (beads_l)) = n_pre)) (PreH4 : ((Zlength (beads_l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH6 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH7 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (intArray.undef_full ( &( "dp" ) ) 40000)
  ** (intArray.undef_full ( &( "vals" ) ) 200)
|--
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ” &&
  “ (Forall2 Eq (sublist ((0 : Int)) ((0 : Int)) ((@List.nil Int))) (sublist ((0 : Int)) ((0 : Int)) (beads_l))) ” &&
  “ ((Zlength ((@List.nil Int))) = (0 : Int)) ”
  &&  (intArray.undef_seg ( &( "vals" ) ) (0 : Int) (2 * n_pre))
  ** (intArray.undef_full ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)))
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
)

noncomputable def energyNecklace_entail_wit_1_split_goal_1 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (PreH1 : (4 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (beads_l)) = n_pre)) (PreH4 : ((Zlength (beads_l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH6 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH7 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (intArray.undef_full ( &( "dp" ) ) 40000)
  ** (intArray.undef_full ( &( "vals" ) ) 200)
|--
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”

noncomputable def energyNecklace_entail_wit_1_split_goal_2 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (PreH1 : (4 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (beads_l)) = n_pre)) (PreH4 : ((Zlength (beads_l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH6 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH7 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (intArray.undef_full ( &( "dp" ) ) 40000)
  ** (intArray.undef_full ( &( "vals" ) ) 200)
|--
  “ (Forall2 Eq (sublist ((0 : Int)) ((0 : Int)) ((@List.nil Int))) (sublist ((0 : Int)) ((0 : Int)) (beads_l))) ”

noncomputable def energyNecklace_entail_wit_1_split_goal_3 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (PreH1 : (4 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (beads_l)) = n_pre)) (PreH4 : ((Zlength (beads_l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH6 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH7 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (intArray.undef_full ( &( "dp" ) ) 40000)
  ** (intArray.undef_full ( &( "vals" ) ) 200)
|--
  “ ((Zlength ((@List.nil Int))) = (0 : Int)) ”

noncomputable def energyNecklace_entail_wit_1_split_goal_spatial : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (PreH1 : (4 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (beads_l)) = n_pre)) (PreH4 : ((Zlength (beads_l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH6 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH7 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (intArray.undef_full ( &( "dp" ) ) 40000)
  ** (intArray.undef_full ( &( "vals" ) ) 200)
|--
  (intArray.undef_seg ( &( "vals" ) ) (0 : Int) (2 * n_pre))
  ** (intArray.undef_full ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)))
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)

noncomputable def energyNecklace_entail_wit_2 : Prop :=
  (
forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (i : Int) (vals_l_2 : (List Int)) (width : Int) (total : Int) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 Eq (sublist ((0 : Int)) (i) (vals_l_2)) (sublist ((0 : Int)) (i) (beads_l)))) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH15 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH16 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  (intArray.seg ( &( "vals" ) ) (0 : Int) (i + 1) (vals_l_2 ++ ((Znth i beads_l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "vals" ) ) (i + 1) total)
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.undef_full ( &( "dp" ) ) (total * width))
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  EX vals_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (vals_l)) = (i + 1)) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ (Forall2 Eq (sublist ((0 : Int)) ((i + 1)) (vals_l)) (sublist ((0 : Int)) ((i + 1)) (beads_l))) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) beads_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) beads_l) ” &&
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.seg ( &( "vals" ) ) (0 : Int) (i + 1) vals_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (i + 1) total)
  ** (intArray.undef_full ( &( "dp" ) ) (total * width))
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
) \/
(
forall (beads_l : (List Int)) (n_pre : Int) (i : Int) (vals_l_2 : (List Int)) (width : Int) (total : Int) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 Eq (sublist ((0 : Int)) (i) (vals_l_2)) (sublist ((0 : Int)) (i) (beads_l)))) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH15 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH16 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  TT && emp 
|--
  “ (Forall2 Eq (sublist ((0 : Int)) ((i + 1)) ((vals_l_2 ++ ((Znth i beads_l (0 : Int)) :: (@List.nil Int))))) (sublist ((0 : Int)) ((i + 1)) (beads_l))) ” &&
  “ ((Zlength ((vals_l_2 ++ ((Znth i beads_l (0 : Int)) :: (@List.nil Int))))) = (i + 1)) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_2_split_goal_1 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (i : Int) (vals_l_2 : (List Int)) (width : Int) (total : Int) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 Eq (sublist ((0 : Int)) (i) (vals_l_2)) (sublist ((0 : Int)) (i) (beads_l)))) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH15 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH16 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  (Forall2 Eq (sublist ((0 : Int)) ((i + 1)) ((vals_l_2 ++ ((Znth i beads_l (0 : Int)) :: (@List.nil Int))))) (sublist ((0 : Int)) ((i + 1)) (beads_l)))

noncomputable def energyNecklace_entail_wit_2_split_goal_2 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (i : Int) (vals_l_2 : (List Int)) (width : Int) (total : Int) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 Eq (sublist ((0 : Int)) (i) (vals_l_2)) (sublist ((0 : Int)) (i) (beads_l)))) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH15 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH16 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((Zlength ((vals_l_2 ++ ((Znth i beads_l (0 : Int)) :: (@List.nil Int))))) = (i + 1))

noncomputable def energyNecklace_entail_wit_3 : Prop :=
  (
forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (i : Int) (vals_l_2 : (List Int)) (width : Int) (total : Int) (PreH1 : (i >= n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 Eq (sublist ((0 : Int)) (i) (vals_l_2)) (sublist ((0 : Int)) (i) (beads_l)))) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH15 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH16 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.seg ( &( "vals" ) ) (0 : Int) i vals_l_2)
  ** (intArray.undef_seg ( &( "vals" ) ) i total)
  ** (intArray.undef_full ( &( "dp" ) ) (total * width))
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  EX vals_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (vals_l)) = (n_pre + (0 : Int))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (Forall2 Eq (sublist ((0 : Int)) (n_pre) (vals_l)) (sublist ((0 : Int)) (n_pre) (beads_l))) ” &&
  “ (Forall2 Eq (sublist (n_pre) ((n_pre + (0 : Int))) (vals_l)) (sublist ((0 : Int)) ((0 : Int)) (beads_l))) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) beads_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) beads_l) ” &&
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.seg ( &( "vals" ) ) (0 : Int) (n_pre + (0 : Int)) vals_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (n_pre + (0 : Int)) total)
  ** (intArray.undef_full ( &( "dp" ) ) (total * width))
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
) \/
(
forall (beads_l : (List Int)) (n_pre : Int) (i : Int) (vals_l_2 : (List Int)) (width : Int) (total : Int) (PreH1 : (i >= n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 Eq (sublist ((0 : Int)) (i) (vals_l_2)) (sublist ((0 : Int)) (i) (beads_l)))) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH15 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH16 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (intArray.seg ( &( "vals" ) ) (0 : Int) i vals_l_2)
|--
  EX vals_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (vals_l)) = (n_pre + (0 : Int))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (Forall2 Eq (sublist ((0 : Int)) (n_pre) (vals_l)) (sublist ((0 : Int)) (n_pre) (beads_l))) ” &&
  “ (Forall2 Eq (sublist (n_pre) ((n_pre + (0 : Int))) (vals_l)) (sublist ((0 : Int)) ((0 : Int)) (beads_l))) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) beads_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) beads_l) ” &&
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  (intArray.seg ( &( "vals" ) ) (0 : Int) (n_pre + (0 : Int)) vals_l)
)

noncomputable def energyNecklace_entail_wit_4 : Prop :=
  (
forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (i : Int) (vals_l_2 : (List Int)) (width : Int) (total : Int) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = (n_pre + i))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 Eq (sublist ((0 : Int)) (n_pre) (vals_l_2)) (sublist ((0 : Int)) (n_pre) (beads_l)))) (PreH13 : (Forall2 Eq (sublist (n_pre) ((n_pre + i)) (vals_l_2)) (sublist ((0 : Int)) (i) (beads_l)))) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH16 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH17 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  (intArray.seg ( &( "vals" ) ) (0 : Int) ((n_pre + i) + 1) (vals_l_2 ++ ((Znth i beads_l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "vals" ) ) ((n_pre + i) + 1) total)
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.undef_full ( &( "dp" ) ) (total * width))
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  EX vals_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (vals_l)) = (n_pre + (i + 1))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ (Forall2 Eq (sublist ((0 : Int)) (n_pre) (vals_l)) (sublist ((0 : Int)) (n_pre) (beads_l))) ” &&
  “ (Forall2 Eq (sublist (n_pre) ((n_pre + (i + 1))) (vals_l)) (sublist ((0 : Int)) ((i + 1)) (beads_l))) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) beads_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) beads_l) ” &&
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.seg ( &( "vals" ) ) (0 : Int) (n_pre + (i + 1)) vals_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (n_pre + (i + 1)) total)
  ** (intArray.undef_full ( &( "dp" ) ) (total * width))
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
) \/
(
forall (beads_l : (List Int)) (n_pre : Int) (i : Int) (vals_l_2 : (List Int)) (width : Int) (total : Int) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = (n_pre + i))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 Eq (sublist ((0 : Int)) (n_pre) (vals_l_2)) (sublist ((0 : Int)) (n_pre) (beads_l)))) (PreH13 : (Forall2 Eq (sublist (n_pre) ((n_pre + i)) (vals_l_2)) (sublist ((0 : Int)) (i) (beads_l)))) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH16 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH17 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  (intArray.seg ( &( "vals" ) ) (0 : Int) ((n_pre + i) + 1) (vals_l_2 ++ ((Znth i beads_l (0 : Int)) :: (@List.nil Int))))
|--
  EX vals_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (vals_l)) = (n_pre + (i + 1))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ (Forall2 Eq (sublist ((0 : Int)) (n_pre) (vals_l)) (sublist ((0 : Int)) (n_pre) (beads_l))) ” &&
  “ (Forall2 Eq (sublist (n_pre) ((n_pre + (i + 1))) (vals_l)) (sublist ((0 : Int)) ((i + 1)) (beads_l))) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) beads_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) beads_l) ” &&
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  (intArray.seg ( &( "vals" ) ) (0 : Int) (n_pre + (i + 1)) vals_l)
)

noncomputable def energyNecklace_entail_wit_5 : Prop :=
  (
forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (i : Int) (vals_l_2 : (List Int)) (width : Int) (total : Int) (PreH1 : (i >= n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = (n_pre + i))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 Eq (sublist ((0 : Int)) (n_pre) (vals_l_2)) (sublist ((0 : Int)) (n_pre) (beads_l)))) (PreH13 : (Forall2 Eq (sublist (n_pre) ((n_pre + i)) (vals_l_2)) (sublist ((0 : Int)) (i) (beads_l)))) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH16 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH17 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.seg ( &( "vals" ) ) (0 : Int) (n_pre + i) vals_l_2)
  ** (intArray.undef_seg ( &( "vals" ) ) (n_pre + i) total)
  ** (intArray.undef_full ( &( "dp" ) ) (total * width))
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (total * width)) ” &&
  “ (Forall (Eq ((0 : Int))) dp_l) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) beads_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) beads_l) ” &&
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) (0 : Int) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (0 : Int) (total * width))
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
) \/
(
forall (beads_l : (List Int)) (n_pre : Int) (i : Int) (vals_l_2 : (List Int)) (width : Int) (total : Int) (PreH1 : (i >= n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = (n_pre + i))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 Eq (sublist ((0 : Int)) (n_pre) (vals_l_2)) (sublist ((0 : Int)) (n_pre) (beads_l)))) (PreH13 : (Forall2 Eq (sublist (n_pre) ((n_pre + i)) (vals_l_2)) (sublist ((0 : Int)) (i) (beads_l)))) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH16 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH17 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  TT && emp 
|--
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l_2 n_pre) ” &&
  “ (Forall (Eq ((0 : Int))) (@List.nil Int)) ” &&
  “ ((Zlength ((@List.nil Int))) = (0 : Int)) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_5_split_goal_1 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (i : Int) (vals_l_2 : (List Int)) (width : Int) (total : Int) (PreH1 : (i >= n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = (n_pre + i))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 Eq (sublist ((0 : Int)) (n_pre) (vals_l_2)) (sublist ((0 : Int)) (n_pre) (beads_l)))) (PreH13 : (Forall2 Eq (sublist (n_pre) ((n_pre + i)) (vals_l_2)) (sublist ((0 : Int)) (i) (beads_l)))) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH16 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH17 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))

noncomputable def energyNecklace_entail_wit_5_split_goal_2 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (i : Int) (vals_l_2 : (List Int)) (width : Int) (total : Int) (PreH1 : (i >= n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = (n_pre + i))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 Eq (sublist ((0 : Int)) (n_pre) (vals_l_2)) (sublist ((0 : Int)) (n_pre) (beads_l)))) (PreH13 : (Forall2 Eq (sublist (n_pre) ((n_pre + i)) (vals_l_2)) (sublist ((0 : Int)) (i) (beads_l)))) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH16 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH17 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (EnergyValsDuplicated beads_l vals_l_2 n_pre)

noncomputable def energyNecklace_entail_wit_5_split_goal_3 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (i : Int) (vals_l_2 : (List Int)) (width : Int) (total : Int) (PreH1 : (i >= n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = (n_pre + i))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 Eq (sublist ((0 : Int)) (n_pre) (vals_l_2)) (sublist ((0 : Int)) (n_pre) (beads_l)))) (PreH13 : (Forall2 Eq (sublist (n_pre) ((n_pre + i)) (vals_l_2)) (sublist ((0 : Int)) (i) (beads_l)))) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH16 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH17 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (Forall (Eq ((0 : Int))) (@List.nil Int))

noncomputable def energyNecklace_entail_wit_5_split_goal_4 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (i : Int) (vals_l_2 : (List Int)) (width : Int) (total : Int) (PreH1 : (i >= n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = (n_pre + i))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 Eq (sublist ((0 : Int)) (n_pre) (vals_l_2)) (sublist ((0 : Int)) (n_pre) (beads_l)))) (PreH13 : (Forall2 Eq (sublist (n_pre) ((n_pre + i)) (vals_l_2)) (sublist ((0 : Int)) (i) (beads_l)))) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH16 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH17 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  ((Zlength ((@List.nil Int))) = (0 : Int))

noncomputable def energyNecklace_entail_wit_6 : Prop :=
  (
forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l_2 : (List Int)) (i : Int) (dp_l_2 : (List Int)) (width : Int) (total : Int) (PreH1 : (i < (total * width))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (total * width))) (PreH12 : (Forall (Eq ((0 : Int))) dp_l_2)) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH16 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH17 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  (intArray.seg ( &( "dp" ) ) (0 : Int) (i + 1) (dp_l_2 ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "dp" ) ) (i + 1) (total * width))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l_2)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (i + 1)) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (total * width)) ” &&
  “ (Forall (Eq ((0 : Int))) dp_l) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) beads_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) beads_l) ” &&
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) (i + 1) dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) (i + 1) (total * width))
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
) \/
(
forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (i : Int) (dp_l_2 : (List Int)) (width : Int) (total : Int) (PreH1 : (i < (total * width))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (total * width))) (PreH12 : (Forall (Eq ((0 : Int))) dp_l_2)) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH16 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH17 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  TT && emp 
|--
  “ (Forall (Eq ((0 : Int))) (dp_l_2 ++ ((0 : Int) :: (@List.nil Int)))) ” &&
  “ ((Zlength ((dp_l_2 ++ ((0 : Int) :: (@List.nil Int))))) = (i + 1)) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_6_split_goal_1 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (i : Int) (dp_l_2 : (List Int)) (width : Int) (total : Int) (PreH1 : (i < (total * width))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (total * width))) (PreH12 : (Forall (Eq ((0 : Int))) dp_l_2)) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH16 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH17 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  (Forall (Eq ((0 : Int))) (dp_l_2 ++ ((0 : Int) :: (@List.nil Int))))

noncomputable def energyNecklace_entail_wit_6_split_goal_2 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (i : Int) (dp_l_2 : (List Int)) (width : Int) (total : Int) (PreH1 : (i < (total * width))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (total * width))) (PreH12 : (Forall (Eq ((0 : Int))) dp_l_2)) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH16 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH17 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((Zlength ((dp_l_2 ++ ((0 : Int) :: (@List.nil Int))))) = (i + 1))

noncomputable def energyNecklace_entail_wit_7 : Prop :=
  (
forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l_2 : (List Int)) (i : Int) (dp_l_2 : (List Int)) (width : Int) (total : Int) (PreH1 : (i >= (total * width))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (total * width))) (PreH12 : (Forall (Eq ((0 : Int))) dp_l_2)) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH16 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH17 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l_2)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) i dp_l_2)
  ** (intArray.undef_seg ( &( "dp" ) ) i (total * width))
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ (2 <= 2) ” &&
  “ (2 <= (n_pre + 1)) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (width = total) ” &&
  “ ((Zlength (vals_l)) = total) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (1 <= 2) ” &&
  “ (EnergyLengthsComplete vals_l dp_l width 2) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) beads_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) beads_l) ” &&
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
) \/
(
forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (i : Int) (dp_l_2 : (List Int)) (width : Int) (total : Int) (PreH1 : (i >= (total * width))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (total * width))) (PreH12 : (Forall (Eq ((0 : Int))) dp_l_2)) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH16 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH17 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  TT && emp 
|--
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ” &&
  “ (EnergyLengthsComplete vals_l_2 dp_l_2 width 2) ” &&
  “ ((Zlength (vals_l_2)) = (2 * n_pre)) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_7_split_goal_1 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (i : Int) (dp_l_2 : (List Int)) (width : Int) (total : Int) (PreH1 : (i >= (total * width))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (total * width))) (PreH12 : (Forall (Eq ((0 : Int))) dp_l_2)) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH16 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH17 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))

noncomputable def energyNecklace_entail_wit_7_split_goal_2 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (i : Int) (dp_l_2 : (List Int)) (width : Int) (total : Int) (PreH1 : (i >= (total * width))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (total * width))) (PreH12 : (Forall (Eq ((0 : Int))) dp_l_2)) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH16 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH17 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (EnergyLengthsComplete vals_l_2 dp_l_2 width 2)

noncomputable def energyNecklace_entail_wit_7_split_goal_3 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (i : Int) (dp_l_2 : (List Int)) (width : Int) (total : Int) (PreH1 : (i >= (total * width))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (total * width))) (PreH12 : (Forall (Eq ((0 : Int))) dp_l_2)) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH16 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH17 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  ((Zlength (vals_l_2)) = (2 * n_pre))

noncomputable def energyNecklace_entail_wit_8 : Prop :=
  (
forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (len : Int) (width : Int) (total : Int) (PreH1 : (len <= n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l_2)) = (total * width))) (PreH12 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (width = total)) (PreH15 : ((Zlength (vals_l_2)) = total)) (PreH16 : ((Zlength (dp_l_2)) = (total * width))) (PreH17 : (1 <= len)) (PreH18 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH19 : ((Zlength (beads_l)) = n_pre)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH22 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l_2)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l_2)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (total - len)) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (width = total) ” &&
  “ ((Zlength (vals_l)) = total) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (1 <= len) ” &&
  “ (EnergyLengthsComplete vals_l dp_l width len) ” &&
  “ (2 <= len) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ (EnergyLeftComplete vals_l dp_l width len (0 : Int)) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) beads_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) beads_l) ” &&
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
) \/
(
forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (len : Int) (width : Int) (total : Int) (PreH1 : (len <= n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l_2)) = (total * width))) (PreH12 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (width = total)) (PreH15 : ((Zlength (vals_l_2)) = total)) (PreH16 : ((Zlength (dp_l_2)) = (total * width))) (PreH17 : (1 <= len)) (PreH18 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH19 : ((Zlength (beads_l)) = n_pre)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH22 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  TT && emp 
|--
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ” &&
  “ (EnergyLeftComplete vals_l_2 dp_l_2 width len (0 : Int)) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_8_split_goal_1 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (len : Int) (width : Int) (total : Int) (PreH1 : (len <= n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l_2)) = (total * width))) (PreH12 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (width = total)) (PreH15 : ((Zlength (vals_l_2)) = total)) (PreH16 : ((Zlength (dp_l_2)) = (total * width))) (PreH17 : (1 <= len)) (PreH18 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH19 : ((Zlength (beads_l)) = n_pre)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH22 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))

noncomputable def energyNecklace_entail_wit_8_split_goal_2 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (len : Int) (width : Int) (total : Int) (PreH1 : (len <= n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l_2)) = (total * width))) (PreH12 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (width = total)) (PreH15 : ((Zlength (vals_l_2)) = total)) (PreH16 : ((Zlength (dp_l_2)) = (total * width))) (PreH17 : (1 <= len)) (PreH18 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH19 : ((Zlength (beads_l)) = n_pre)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH22 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (EnergyLeftComplete vals_l_2 dp_l_2 width len (0 : Int))

noncomputable def energyNecklace_entail_wit_9 : Prop :=
  (
forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (left < (total - len))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= (total - len))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l_2)) = total)) (PreH18 : ((Zlength (dp_l_2)) = (total * width))) (PreH19 : (1 <= len)) (PreH20 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH21 : (2 <= len)) (PreH22 : ((0 : Int) <= left)) (PreH23 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH26 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH27 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l_2)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l_2)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (total - len)) ” &&
  “ (((left + len) - 1) = ((left + len) - 1)) ” &&
  “ (left < ((left + len) - 1)) ” &&
  “ ((0 : Int) <= ((left + len) - 1)) ” &&
  “ (((left + len) - 1) < total) ” &&
  “ ((((left + len) - 1) + 1) < total) ” &&
  “ (left <= left) ” &&
  “ (left <= ((left + len) - 1)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 2100000000) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (width = total) ” &&
  “ ((Zlength (vals_l)) = total) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (1 <= len) ” &&
  “ (EnergyLengthsComplete vals_l dp_l width len) ” &&
  “ (2 <= len) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (EnergyLeftComplete vals_l dp_l width len left) ” &&
  “ ((left + len) <= total) ” &&
  “ (left <= left) ” &&
  “ (left <= ((left + len) - 1)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 2100000000) ” &&
  “ (EnergySplitBest vals_l dp_l width len left left (0 : Int)) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) beads_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) beads_l) ” &&
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
) \/
(
forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (left < (total - len))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= (total - len))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l_2)) = total)) (PreH18 : ((Zlength (dp_l_2)) = (total * width))) (PreH19 : (1 <= len)) (PreH20 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH21 : (2 <= len)) (PreH22 : ((0 : Int) <= left)) (PreH23 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH26 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH27 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  TT && emp 
|--
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ” &&
  “ (EnergySplitBest vals_l_2 dp_l_2 width len left left (0 : Int)) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_9_split_goal_1 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (left < (total - len))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= (total - len))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l_2)) = total)) (PreH18 : ((Zlength (dp_l_2)) = (total * width))) (PreH19 : (1 <= len)) (PreH20 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH21 : (2 <= len)) (PreH22 : ((0 : Int) <= left)) (PreH23 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH26 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH27 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))

noncomputable def energyNecklace_entail_wit_9_split_goal_2 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (left < (total - len))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= (total - len))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l_2)) = total)) (PreH18 : ((Zlength (dp_l_2)) = (total * width))) (PreH19 : (1 <= len)) (PreH20 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH21 : (2 <= len)) (PreH22 : ((0 : Int) <= left)) (PreH23 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH26 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH27 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (EnergySplitBest vals_l_2 dp_l_2 width len left left (0 : Int))

noncomputable def energyNecklace_entail_wit_10 : Prop :=
  (
forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (split < right)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < (total - len))) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : ((0 : Int) <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH24 : ((0 : Int) <= total)) (PreH25 : (width = total)) (PreH26 : ((Zlength (vals_l_2)) = total)) (PreH27 : ((Zlength (dp_l_2)) = (total * width))) (PreH28 : (1 <= len)) (PreH29 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH30 : (2 <= len)) (PreH31 : ((0 : Int) <= left)) (PreH32 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left)) (PreH33 : ((left + len) <= total)) (PreH34 : (left <= split)) (PreH35 : (split <= ((left + len) - 1))) (PreH36 : ((0 : Int) <= best)) (PreH37 : (best <= 2100000000)) (PreH38 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best)) (PreH39 : ((Zlength (beads_l)) = n_pre)) (PreH40 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH41 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH42 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l_2)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l_2)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (total - len)) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left <= split) ” &&
  “ (split < right) ” &&
  “ ((0 : Int) <= right) ” &&
  “ (right < total) ” &&
  “ ((right + 1) < total) ” &&
  “ ((0 : Int) <= ((left * width) + split)) ” &&
  “ (((left * width) + split) < (total * width)) ” &&
  “ ((0 : Int) <= (((split + 1) * width) + right)) ” &&
  “ ((((split + 1) * width) + right) < (total * width)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < total) ” &&
  “ ((0 : Int) <= (split + 1)) ” &&
  “ ((split + 1) < total) ” &&
  “ ((0 : Int) <= (right + 1)) ” &&
  “ ((right + 1) < total) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (width = total) ” &&
  “ ((Zlength (vals_l)) = total) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (1 <= len) ” &&
  “ (EnergyLengthsComplete vals_l dp_l width len) ” &&
  “ (2 <= len) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (EnergyLeftComplete vals_l dp_l width len left) ” &&
  “ ((left + len) <= total) ” &&
  “ (left <= split) ” &&
  “ (split <= ((left + len) - 1)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 2100000000) ” &&
  “ (EnergySplitBest vals_l dp_l width len left split best) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) beads_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) beads_l) ” &&
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
) \/
(
forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (split < right)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < (total - len))) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : ((0 : Int) <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH24 : ((0 : Int) <= total)) (PreH25 : (width = total)) (PreH26 : ((Zlength (vals_l_2)) = total)) (PreH27 : ((Zlength (dp_l_2)) = (total * width))) (PreH28 : (1 <= len)) (PreH29 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH30 : (2 <= len)) (PreH31 : ((0 : Int) <= left)) (PreH32 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left)) (PreH33 : ((left + len) <= total)) (PreH34 : (left <= split)) (PreH35 : (split <= ((left + len) - 1))) (PreH36 : ((0 : Int) <= best)) (PreH37 : (best <= 2100000000)) (PreH38 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best)) (PreH39 : ((Zlength (beads_l)) = n_pre)) (PreH40 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH41 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH42 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  TT && emp 
|--
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ” &&
  “ ((((split + 1) * width) + ((left + len) - 1)) < ((2 * n_pre) * width)) ” &&
  “ (((left * width) + split) < ((2 * n_pre) * width)) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_10_split_goal_1 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (split < right)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < (total - len))) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : ((0 : Int) <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH24 : ((0 : Int) <= total)) (PreH25 : (width = total)) (PreH26 : ((Zlength (vals_l_2)) = total)) (PreH27 : ((Zlength (dp_l_2)) = (total * width))) (PreH28 : (1 <= len)) (PreH29 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH30 : (2 <= len)) (PreH31 : ((0 : Int) <= left)) (PreH32 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left)) (PreH33 : ((left + len) <= total)) (PreH34 : (left <= split)) (PreH35 : (split <= ((left + len) - 1))) (PreH36 : ((0 : Int) <= best)) (PreH37 : (best <= 2100000000)) (PreH38 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best)) (PreH39 : ((Zlength (beads_l)) = n_pre)) (PreH40 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH41 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH42 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))

noncomputable def energyNecklace_entail_wit_10_split_goal_2 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (split < right)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < (total - len))) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : ((0 : Int) <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH24 : ((0 : Int) <= total)) (PreH25 : (width = total)) (PreH26 : ((Zlength (vals_l_2)) = total)) (PreH27 : ((Zlength (dp_l_2)) = (total * width))) (PreH28 : (1 <= len)) (PreH29 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH30 : (2 <= len)) (PreH31 : ((0 : Int) <= left)) (PreH32 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left)) (PreH33 : ((left + len) <= total)) (PreH34 : (left <= split)) (PreH35 : (split <= ((left + len) - 1))) (PreH36 : ((0 : Int) <= best)) (PreH37 : (best <= 2100000000)) (PreH38 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best)) (PreH39 : ((Zlength (beads_l)) = n_pre)) (PreH40 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH41 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH42 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  ((((split + 1) * width) + ((left + len) - 1)) < ((2 * n_pre) * width))

noncomputable def energyNecklace_entail_wit_10_split_goal_3 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (split < right)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < (total - len))) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : ((0 : Int) <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH24 : ((0 : Int) <= total)) (PreH25 : (width = total)) (PreH26 : ((Zlength (vals_l_2)) = total)) (PreH27 : ((Zlength (dp_l_2)) = (total * width))) (PreH28 : (1 <= len)) (PreH29 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH30 : (2 <= len)) (PreH31 : ((0 : Int) <= left)) (PreH32 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left)) (PreH33 : ((left + len) <= total)) (PreH34 : (left <= split)) (PreH35 : (split <= ((left + len) - 1))) (PreH36 : ((0 : Int) <= best)) (PreH37 : (best <= 2100000000)) (PreH38 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best)) (PreH39 : ((Zlength (beads_l)) = n_pre)) (PreH40 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH41 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH42 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (((left * width) + split) < ((2 * n_pre) * width))

noncomputable def energyNecklace_entail_wit_11 : Prop :=
  (
forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : ((0 : Int) <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH36 : (2 <= len)) (PreH37 : ((0 : Int) <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH39 : ((left + len) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len) - 1))) (PreH42 : ((0 : Int) <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best)) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH48 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  EX vals_l_2 : (List Int), EX dp_l_2 : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (total - len)) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left <= split) ” &&
  “ (split < right) ” &&
  “ ((0 : Int) <= right) ” &&
  “ (right < total) ” &&
  “ ((right + 1) < total) ” &&
  “ ((Znth ((left * width) + split) dp_l (0 : Int)) = (Znth ((left * width) + split) dp_l_2 (0 : Int))) ” &&
  “ ((Znth (((split + 1) * width) + right) dp_l (0 : Int)) = (Znth (((split + 1) * width) + right) dp_l_2 (0 : Int))) ” &&
  “ ((((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int))) = (((Znth left vals_l_2 (0 : Int)) * (Znth (split + 1) vals_l_2 (0 : Int))) * (Znth (right + 1) vals_l_2 (0 : Int)))) ” &&
  “ ((((Znth ((left * width) + split) dp_l (0 : Int)) + (Znth (((split + 1) * width) + right) dp_l (0 : Int))) + (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int)))) = (((Znth ((left * width) + split) dp_l (0 : Int)) + (Znth (((split + 1) * width) + right) dp_l (0 : Int))) + (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int))))) ” &&
  “ ((0 : Int) <= (((Znth ((left * width) + split) dp_l (0 : Int)) + (Znth (((split + 1) * width) + right) dp_l (0 : Int))) + (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int))))) ” &&
  “ ((((Znth ((left * width) + split) dp_l (0 : Int)) + (Znth (((split + 1) * width) + right) dp_l (0 : Int))) + (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int)))) <= 2100000000) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l_2)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l_2 n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (width = total) ” &&
  “ ((Zlength (vals_l_2)) = total) ” &&
  “ ((Zlength (dp_l_2)) = (total * width)) ” &&
  “ (1 <= len) ” &&
  “ (EnergyLengthsComplete vals_l_2 dp_l_2 width len) ” &&
  “ (2 <= len) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (EnergyLeftComplete vals_l_2 dp_l_2 width len left) ” &&
  “ ((left + len) <= total) ” &&
  “ (left <= split) ” &&
  “ (split <= ((left + len) - 1)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 2100000000) ” &&
  “ (EnergySplitBest vals_l_2 dp_l_2 width len left split best) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) beads_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) beads_l) ” &&
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l_2)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l_2)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
) \/
(
forall (beads_l : (List Int)) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : ((0 : Int) <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH36 : (2 <= len)) (PreH37 : ((0 : Int) <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH39 : ((left + len) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len) - 1))) (PreH42 : ((0 : Int) <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best)) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH48 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  TT && emp 
|--
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ” &&
  “ ((((Znth ((left * total) + split) dp_l (0 : Int)) + (Znth (((split + 1) * total) + ((left + len) - 1)) dp_l (0 : Int))) + (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (((left + len) - 1) + 1) vals_l (0 : Int)))) <= 2100000000) ” &&
  “ ((0 : Int) <= (((Znth ((left * total) + split) dp_l (0 : Int)) + (Znth (((split + 1) * total) + ((left + len) - 1)) dp_l (0 : Int))) + (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (((left + len) - 1) + 1) vals_l (0 : Int))))) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_11_split_goal_1 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : ((0 : Int) <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH36 : (2 <= len)) (PreH37 : ((0 : Int) <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH39 : ((left + len) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len) - 1))) (PreH42 : ((0 : Int) <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best)) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH48 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))

noncomputable def energyNecklace_entail_wit_11_split_goal_2 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : ((0 : Int) <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH36 : (2 <= len)) (PreH37 : ((0 : Int) <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH39 : ((left + len) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len) - 1))) (PreH42 : ((0 : Int) <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best)) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH48 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  ((((Znth ((left * total) + split) dp_l (0 : Int)) + (Znth (((split + 1) * total) + ((left + len) - 1)) dp_l (0 : Int))) + (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (((left + len) - 1) + 1) vals_l (0 : Int)))) <= 2100000000)

noncomputable def energyNecklace_entail_wit_11_split_goal_3 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : ((0 : Int) <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH36 : (2 <= len)) (PreH37 : ((0 : Int) <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH39 : ((left + len) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len) - 1))) (PreH42 : ((0 : Int) <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best)) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH48 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  ((0 : Int) <= (((Znth ((left * total) + split) dp_l (0 : Int)) + (Znth (((split + 1) * total) + ((left + len) - 1)) dp_l (0 : Int))) + (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (((left + len) - 1) + 1) vals_l (0 : Int)))))

noncomputable def energyNecklace_entail_wit_12_1 : Prop :=
  (
forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (right_value : Int) (gain : Int) (candidate : Int) (best : Int) (PreH1 : (candidate > best)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < (total - len))) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left <= split)) (PreH14 : (split < right)) (PreH15 : ((0 : Int) <= right)) (PreH16 : (right < total)) (PreH17 : ((right + 1) < total)) (PreH18 : (left_value = (Znth ((left * width) + split) dp_l_2 (0 : Int)))) (PreH19 : (right_value = (Znth (((split + 1) * width) + right) dp_l_2 (0 : Int)))) (PreH20 : (gain = (((Znth left vals_l_2 (0 : Int)) * (Znth (split + 1) vals_l_2 (0 : Int))) * (Znth (right + 1) vals_l_2 (0 : Int))))) (PreH21 : (candidate = ((left_value + right_value) + gain))) (PreH22 : ((0 : Int) <= candidate)) (PreH23 : (candidate <= 2100000000)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : ((Zlength (dp_l_2)) = (total * width))) (PreH26 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH27 : ((0 : Int) <= total)) (PreH28 : (width = total)) (PreH29 : ((Zlength (vals_l_2)) = total)) (PreH30 : ((Zlength (dp_l_2)) = (total * width))) (PreH31 : (1 <= len)) (PreH32 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH33 : (2 <= len)) (PreH34 : ((0 : Int) <= left)) (PreH35 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left)) (PreH36 : ((left + len) <= total)) (PreH37 : (left <= split)) (PreH38 : (split <= ((left + len) - 1))) (PreH39 : ((0 : Int) <= best)) (PreH40 : (best <= 2100000000)) (PreH41 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best)) (PreH42 : ((Zlength (beads_l)) = n_pre)) (PreH43 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH45 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l_2)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l_2)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (total - len)) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left <= split) ” &&
  “ (split < right) ” &&
  “ ((right + 1) < total) ” &&
  “ (left_value = (Znth ((left * width) + split) dp_l (0 : Int))) ” &&
  “ (right_value = (Znth (((split + 1) * width) + right) dp_l (0 : Int))) ” &&
  “ (gain = (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int)))) ” &&
  “ (candidate = ((left_value + right_value) + gain)) ” &&
  “ ((0 : Int) <= candidate) ” &&
  “ (candidate <= 2100000000) ” &&
  “ ((0 : Int) <= candidate) ” &&
  “ (candidate <= 2100000000) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (width = total) ” &&
  “ ((Zlength (vals_l)) = total) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (1 <= len) ” &&
  “ (EnergyLengthsComplete vals_l dp_l width len) ” &&
  “ (2 <= len) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (EnergyLeftComplete vals_l dp_l width len left) ” &&
  “ ((left + len) <= total) ” &&
  “ (left <= (split + 1)) ” &&
  “ ((split + 1) <= ((left + len) - 1)) ” &&
  “ ((0 : Int) <= candidate) ” &&
  “ (candidate <= 2100000000) ” &&
  “ (EnergySplitBest vals_l dp_l width len left (split + 1) candidate) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) beads_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) beads_l) ” &&
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
) \/
(
forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (right_value : Int) (gain : Int) (candidate : Int) (best : Int) (PreH1 : (candidate > best)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < (total - len))) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left <= split)) (PreH14 : (split < right)) (PreH15 : ((0 : Int) <= right)) (PreH16 : (right < total)) (PreH17 : ((right + 1) < total)) (PreH18 : (left_value = (Znth ((left * width) + split) dp_l_2 (0 : Int)))) (PreH19 : (right_value = (Znth (((split + 1) * width) + right) dp_l_2 (0 : Int)))) (PreH20 : (gain = (((Znth left vals_l_2 (0 : Int)) * (Znth (split + 1) vals_l_2 (0 : Int))) * (Znth (right + 1) vals_l_2 (0 : Int))))) (PreH21 : (candidate = ((left_value + right_value) + gain))) (PreH22 : ((0 : Int) <= candidate)) (PreH23 : (candidate <= 2100000000)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : ((Zlength (dp_l_2)) = (total * width))) (PreH26 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH27 : ((0 : Int) <= total)) (PreH28 : (width = total)) (PreH29 : ((Zlength (vals_l_2)) = total)) (PreH30 : ((Zlength (dp_l_2)) = (total * width))) (PreH31 : (1 <= len)) (PreH32 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH33 : (2 <= len)) (PreH34 : ((0 : Int) <= left)) (PreH35 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left)) (PreH36 : ((left + len) <= total)) (PreH37 : (left <= split)) (PreH38 : (split <= ((left + len) - 1))) (PreH39 : ((0 : Int) <= best)) (PreH40 : (best <= 2100000000)) (PreH41 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best)) (PreH42 : ((Zlength (beads_l)) = n_pre)) (PreH43 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH45 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  TT && emp 
|--
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ” &&
  “ (EnergySplitBest vals_l_2 dp_l_2 total len left (split + 1) ((left_value + right_value) + gain)) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_12_1_split_goal_1 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (right_value : Int) (gain : Int) (candidate : Int) (best : Int) (PreH1 : (candidate > best)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < (total - len))) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left <= split)) (PreH14 : (split < right)) (PreH15 : ((0 : Int) <= right)) (PreH16 : (right < total)) (PreH17 : ((right + 1) < total)) (PreH18 : (left_value = (Znth ((left * width) + split) dp_l_2 (0 : Int)))) (PreH19 : (right_value = (Znth (((split + 1) * width) + right) dp_l_2 (0 : Int)))) (PreH20 : (gain = (((Znth left vals_l_2 (0 : Int)) * (Znth (split + 1) vals_l_2 (0 : Int))) * (Znth (right + 1) vals_l_2 (0 : Int))))) (PreH21 : (candidate = ((left_value + right_value) + gain))) (PreH22 : ((0 : Int) <= candidate)) (PreH23 : (candidate <= 2100000000)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : ((Zlength (dp_l_2)) = (total * width))) (PreH26 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH27 : ((0 : Int) <= total)) (PreH28 : (width = total)) (PreH29 : ((Zlength (vals_l_2)) = total)) (PreH30 : ((Zlength (dp_l_2)) = (total * width))) (PreH31 : (1 <= len)) (PreH32 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH33 : (2 <= len)) (PreH34 : ((0 : Int) <= left)) (PreH35 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left)) (PreH36 : ((left + len) <= total)) (PreH37 : (left <= split)) (PreH38 : (split <= ((left + len) - 1))) (PreH39 : ((0 : Int) <= best)) (PreH40 : (best <= 2100000000)) (PreH41 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best)) (PreH42 : ((Zlength (beads_l)) = n_pre)) (PreH43 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH45 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))

noncomputable def energyNecklace_entail_wit_12_1_split_goal_2 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (right_value : Int) (gain : Int) (candidate : Int) (best : Int) (PreH1 : (candidate > best)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < (total - len))) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left <= split)) (PreH14 : (split < right)) (PreH15 : ((0 : Int) <= right)) (PreH16 : (right < total)) (PreH17 : ((right + 1) < total)) (PreH18 : (left_value = (Znth ((left * width) + split) dp_l_2 (0 : Int)))) (PreH19 : (right_value = (Znth (((split + 1) * width) + right) dp_l_2 (0 : Int)))) (PreH20 : (gain = (((Znth left vals_l_2 (0 : Int)) * (Znth (split + 1) vals_l_2 (0 : Int))) * (Znth (right + 1) vals_l_2 (0 : Int))))) (PreH21 : (candidate = ((left_value + right_value) + gain))) (PreH22 : ((0 : Int) <= candidate)) (PreH23 : (candidate <= 2100000000)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : ((Zlength (dp_l_2)) = (total * width))) (PreH26 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH27 : ((0 : Int) <= total)) (PreH28 : (width = total)) (PreH29 : ((Zlength (vals_l_2)) = total)) (PreH30 : ((Zlength (dp_l_2)) = (total * width))) (PreH31 : (1 <= len)) (PreH32 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH33 : (2 <= len)) (PreH34 : ((0 : Int) <= left)) (PreH35 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left)) (PreH36 : ((left + len) <= total)) (PreH37 : (left <= split)) (PreH38 : (split <= ((left + len) - 1))) (PreH39 : ((0 : Int) <= best)) (PreH40 : (best <= 2100000000)) (PreH41 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best)) (PreH42 : ((Zlength (beads_l)) = n_pre)) (PreH43 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH45 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (EnergySplitBest vals_l_2 dp_l_2 total len left (split + 1) ((left_value + right_value) + gain))

noncomputable def energyNecklace_entail_wit_12_2 : Prop :=
  (
forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (right_value : Int) (gain : Int) (candidate : Int) (best : Int) (PreH1 : (candidate <= best)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < (total - len))) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left <= split)) (PreH14 : (split < right)) (PreH15 : ((0 : Int) <= right)) (PreH16 : (right < total)) (PreH17 : ((right + 1) < total)) (PreH18 : (left_value = (Znth ((left * width) + split) dp_l_2 (0 : Int)))) (PreH19 : (right_value = (Znth (((split + 1) * width) + right) dp_l_2 (0 : Int)))) (PreH20 : (gain = (((Znth left vals_l_2 (0 : Int)) * (Znth (split + 1) vals_l_2 (0 : Int))) * (Znth (right + 1) vals_l_2 (0 : Int))))) (PreH21 : (candidate = ((left_value + right_value) + gain))) (PreH22 : ((0 : Int) <= candidate)) (PreH23 : (candidate <= 2100000000)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : ((Zlength (dp_l_2)) = (total * width))) (PreH26 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH27 : ((0 : Int) <= total)) (PreH28 : (width = total)) (PreH29 : ((Zlength (vals_l_2)) = total)) (PreH30 : ((Zlength (dp_l_2)) = (total * width))) (PreH31 : (1 <= len)) (PreH32 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH33 : (2 <= len)) (PreH34 : ((0 : Int) <= left)) (PreH35 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left)) (PreH36 : ((left + len) <= total)) (PreH37 : (left <= split)) (PreH38 : (split <= ((left + len) - 1))) (PreH39 : ((0 : Int) <= best)) (PreH40 : (best <= 2100000000)) (PreH41 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best)) (PreH42 : ((Zlength (beads_l)) = n_pre)) (PreH43 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH45 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l_2)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l_2)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (total - len)) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left <= split) ” &&
  “ (split < right) ” &&
  “ ((right + 1) < total) ” &&
  “ (left_value = (Znth ((left * width) + split) dp_l (0 : Int))) ” &&
  “ (right_value = (Znth (((split + 1) * width) + right) dp_l (0 : Int))) ” &&
  “ (gain = (((Znth left vals_l (0 : Int)) * (Znth (split + 1) vals_l (0 : Int))) * (Znth (right + 1) vals_l (0 : Int)))) ” &&
  “ (candidate = ((left_value + right_value) + gain)) ” &&
  “ ((0 : Int) <= candidate) ” &&
  “ (candidate <= 2100000000) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 2100000000) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (width = total) ” &&
  “ ((Zlength (vals_l)) = total) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (1 <= len) ” &&
  “ (EnergyLengthsComplete vals_l dp_l width len) ” &&
  “ (2 <= len) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (EnergyLeftComplete vals_l dp_l width len left) ” &&
  “ ((left + len) <= total) ” &&
  “ (left <= (split + 1)) ” &&
  “ ((split + 1) <= ((left + len) - 1)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 2100000000) ” &&
  “ (EnergySplitBest vals_l dp_l width len left (split + 1) best) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) beads_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) beads_l) ” &&
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
) \/
(
forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (right_value : Int) (gain : Int) (candidate : Int) (best : Int) (PreH1 : (candidate <= best)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < (total - len))) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left <= split)) (PreH14 : (split < right)) (PreH15 : ((0 : Int) <= right)) (PreH16 : (right < total)) (PreH17 : ((right + 1) < total)) (PreH18 : (left_value = (Znth ((left * width) + split) dp_l_2 (0 : Int)))) (PreH19 : (right_value = (Znth (((split + 1) * width) + right) dp_l_2 (0 : Int)))) (PreH20 : (gain = (((Znth left vals_l_2 (0 : Int)) * (Znth (split + 1) vals_l_2 (0 : Int))) * (Znth (right + 1) vals_l_2 (0 : Int))))) (PreH21 : (candidate = ((left_value + right_value) + gain))) (PreH22 : ((0 : Int) <= candidate)) (PreH23 : (candidate <= 2100000000)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : ((Zlength (dp_l_2)) = (total * width))) (PreH26 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH27 : ((0 : Int) <= total)) (PreH28 : (width = total)) (PreH29 : ((Zlength (vals_l_2)) = total)) (PreH30 : ((Zlength (dp_l_2)) = (total * width))) (PreH31 : (1 <= len)) (PreH32 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH33 : (2 <= len)) (PreH34 : ((0 : Int) <= left)) (PreH35 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left)) (PreH36 : ((left + len) <= total)) (PreH37 : (left <= split)) (PreH38 : (split <= ((left + len) - 1))) (PreH39 : ((0 : Int) <= best)) (PreH40 : (best <= 2100000000)) (PreH41 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best)) (PreH42 : ((Zlength (beads_l)) = n_pre)) (PreH43 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH45 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  TT && emp 
|--
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ” &&
  “ (EnergySplitBest vals_l_2 dp_l_2 total len left (split + 1) best) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_12_2_split_goal_1 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (right_value : Int) (gain : Int) (candidate : Int) (best : Int) (PreH1 : (candidate <= best)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < (total - len))) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left <= split)) (PreH14 : (split < right)) (PreH15 : ((0 : Int) <= right)) (PreH16 : (right < total)) (PreH17 : ((right + 1) < total)) (PreH18 : (left_value = (Znth ((left * width) + split) dp_l_2 (0 : Int)))) (PreH19 : (right_value = (Znth (((split + 1) * width) + right) dp_l_2 (0 : Int)))) (PreH20 : (gain = (((Znth left vals_l_2 (0 : Int)) * (Znth (split + 1) vals_l_2 (0 : Int))) * (Znth (right + 1) vals_l_2 (0 : Int))))) (PreH21 : (candidate = ((left_value + right_value) + gain))) (PreH22 : ((0 : Int) <= candidate)) (PreH23 : (candidate <= 2100000000)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : ((Zlength (dp_l_2)) = (total * width))) (PreH26 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH27 : ((0 : Int) <= total)) (PreH28 : (width = total)) (PreH29 : ((Zlength (vals_l_2)) = total)) (PreH30 : ((Zlength (dp_l_2)) = (total * width))) (PreH31 : (1 <= len)) (PreH32 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH33 : (2 <= len)) (PreH34 : ((0 : Int) <= left)) (PreH35 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left)) (PreH36 : ((left + len) <= total)) (PreH37 : (left <= split)) (PreH38 : (split <= ((left + len) - 1))) (PreH39 : ((0 : Int) <= best)) (PreH40 : (best <= 2100000000)) (PreH41 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best)) (PreH42 : ((Zlength (beads_l)) = n_pre)) (PreH43 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH45 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))

noncomputable def energyNecklace_entail_wit_12_2_split_goal_2 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (right_value : Int) (gain : Int) (candidate : Int) (best : Int) (PreH1 : (candidate <= best)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < (total - len))) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left <= split)) (PreH14 : (split < right)) (PreH15 : ((0 : Int) <= right)) (PreH16 : (right < total)) (PreH17 : ((right + 1) < total)) (PreH18 : (left_value = (Znth ((left * width) + split) dp_l_2 (0 : Int)))) (PreH19 : (right_value = (Znth (((split + 1) * width) + right) dp_l_2 (0 : Int)))) (PreH20 : (gain = (((Znth left vals_l_2 (0 : Int)) * (Znth (split + 1) vals_l_2 (0 : Int))) * (Znth (right + 1) vals_l_2 (0 : Int))))) (PreH21 : (candidate = ((left_value + right_value) + gain))) (PreH22 : ((0 : Int) <= candidate)) (PreH23 : (candidate <= 2100000000)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : ((Zlength (dp_l_2)) = (total * width))) (PreH26 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH27 : ((0 : Int) <= total)) (PreH28 : (width = total)) (PreH29 : ((Zlength (vals_l_2)) = total)) (PreH30 : ((Zlength (dp_l_2)) = (total * width))) (PreH31 : (1 <= len)) (PreH32 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH33 : (2 <= len)) (PreH34 : ((0 : Int) <= left)) (PreH35 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left)) (PreH36 : ((left + len) <= total)) (PreH37 : (left <= split)) (PreH38 : (split <= ((left + len) - 1))) (PreH39 : ((0 : Int) <= best)) (PreH40 : (best <= 2100000000)) (PreH41 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best)) (PreH42 : ((Zlength (beads_l)) = n_pre)) (PreH43 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH44 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH45 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (EnergySplitBest vals_l_2 dp_l_2 total len left (split + 1) best)

noncomputable def energyNecklace_entail_wit_13 : Prop :=
  (
forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (right_value : Int) (gain : Int) (candidate : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((right + 1) < total)) (PreH15 : (left_value = (Znth ((left * width) + split) dp_l_2 (0 : Int)))) (PreH16 : (right_value = (Znth (((split + 1) * width) + right) dp_l_2 (0 : Int)))) (PreH17 : (gain = (((Znth left vals_l_2 (0 : Int)) * (Znth (split + 1) vals_l_2 (0 : Int))) * (Znth (right + 1) vals_l_2 (0 : Int))))) (PreH18 : (candidate = ((left_value + right_value) + gain))) (PreH19 : ((0 : Int) <= candidate)) (PreH20 : (candidate <= 2100000000)) (PreH21 : ((0 : Int) <= best)) (PreH22 : (best <= 2100000000)) (PreH23 : ((Zlength (beads_l)) = n_pre)) (PreH24 : ((Zlength (dp_l_2)) = (total * width))) (PreH25 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH26 : ((0 : Int) <= total)) (PreH27 : (width = total)) (PreH28 : ((Zlength (vals_l_2)) = total)) (PreH29 : ((Zlength (dp_l_2)) = (total * width))) (PreH30 : (1 <= len)) (PreH31 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH32 : (2 <= len)) (PreH33 : ((0 : Int) <= left)) (PreH34 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left)) (PreH35 : ((left + len) <= total)) (PreH36 : (left <= (split + 1))) (PreH37 : ((split + 1) <= ((left + len) - 1))) (PreH38 : ((0 : Int) <= best)) (PreH39 : (best <= 2100000000)) (PreH40 : (EnergySplitBest vals_l_2 dp_l_2 width len left (split + 1) best)) (PreH41 : ((Zlength (beads_l)) = n_pre)) (PreH42 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH44 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l_2)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l_2)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (total - len)) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left < right) ” &&
  “ ((0 : Int) <= right) ” &&
  “ (right < total) ” &&
  “ ((right + 1) < total) ” &&
  “ (left <= (split + 1)) ” &&
  “ ((split + 1) <= right) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 2100000000) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (width = total) ” &&
  “ ((Zlength (vals_l)) = total) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (1 <= len) ” &&
  “ (EnergyLengthsComplete vals_l dp_l width len) ” &&
  “ (2 <= len) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (EnergyLeftComplete vals_l dp_l width len left) ” &&
  “ ((left + len) <= total) ” &&
  “ (left <= (split + 1)) ” &&
  “ ((split + 1) <= ((left + len) - 1)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 2100000000) ” &&
  “ (EnergySplitBest vals_l dp_l width len left (split + 1) best) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) beads_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) beads_l) ” &&
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
) \/
(
forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (right_value : Int) (gain : Int) (candidate : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((right + 1) < total)) (PreH15 : (left_value = (Znth ((left * width) + split) dp_l_2 (0 : Int)))) (PreH16 : (right_value = (Znth (((split + 1) * width) + right) dp_l_2 (0 : Int)))) (PreH17 : (gain = (((Znth left vals_l_2 (0 : Int)) * (Znth (split + 1) vals_l_2 (0 : Int))) * (Znth (right + 1) vals_l_2 (0 : Int))))) (PreH18 : (candidate = ((left_value + right_value) + gain))) (PreH19 : ((0 : Int) <= candidate)) (PreH20 : (candidate <= 2100000000)) (PreH21 : ((0 : Int) <= best)) (PreH22 : (best <= 2100000000)) (PreH23 : ((Zlength (beads_l)) = n_pre)) (PreH24 : ((Zlength (dp_l_2)) = (total * width))) (PreH25 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH26 : ((0 : Int) <= total)) (PreH27 : (width = total)) (PreH28 : ((Zlength (vals_l_2)) = total)) (PreH29 : ((Zlength (dp_l_2)) = (total * width))) (PreH30 : (1 <= len)) (PreH31 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH32 : (2 <= len)) (PreH33 : ((0 : Int) <= left)) (PreH34 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left)) (PreH35 : ((left + len) <= total)) (PreH36 : (left <= (split + 1))) (PreH37 : ((split + 1) <= ((left + len) - 1))) (PreH38 : ((0 : Int) <= best)) (PreH39 : (best <= 2100000000)) (PreH40 : (EnergySplitBest vals_l_2 dp_l_2 width len left (split + 1) best)) (PreH41 : ((Zlength (beads_l)) = n_pre)) (PreH42 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH44 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  TT && emp 
|--
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_13_split_goal_1 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (left_value : Int) (right_value : Int) (gain : Int) (candidate : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((right + 1) < total)) (PreH15 : (left_value = (Znth ((left * width) + split) dp_l_2 (0 : Int)))) (PreH16 : (right_value = (Znth (((split + 1) * width) + right) dp_l_2 (0 : Int)))) (PreH17 : (gain = (((Znth left vals_l_2 (0 : Int)) * (Znth (split + 1) vals_l_2 (0 : Int))) * (Znth (right + 1) vals_l_2 (0 : Int))))) (PreH18 : (candidate = ((left_value + right_value) + gain))) (PreH19 : ((0 : Int) <= candidate)) (PreH20 : (candidate <= 2100000000)) (PreH21 : ((0 : Int) <= best)) (PreH22 : (best <= 2100000000)) (PreH23 : ((Zlength (beads_l)) = n_pre)) (PreH24 : ((Zlength (dp_l_2)) = (total * width))) (PreH25 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH26 : ((0 : Int) <= total)) (PreH27 : (width = total)) (PreH28 : ((Zlength (vals_l_2)) = total)) (PreH29 : ((Zlength (dp_l_2)) = (total * width))) (PreH30 : (1 <= len)) (PreH31 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH32 : (2 <= len)) (PreH33 : ((0 : Int) <= left)) (PreH34 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left)) (PreH35 : ((left + len) <= total)) (PreH36 : (left <= (split + 1))) (PreH37 : ((split + 1) <= ((left + len) - 1))) (PreH38 : ((0 : Int) <= best)) (PreH39 : (best <= 2100000000)) (PreH40 : (EnergySplitBest vals_l_2 dp_l_2 width len left (split + 1) best)) (PreH41 : ((Zlength (beads_l)) = n_pre)) (PreH42 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH43 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH44 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))

noncomputable def energyNecklace_entail_wit_14 : Prop :=
  (
forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (split >= right)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < (total - len))) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : ((0 : Int) <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH24 : ((0 : Int) <= total)) (PreH25 : (width = total)) (PreH26 : ((Zlength (vals_l_2)) = total)) (PreH27 : ((Zlength (dp_l_2)) = (total * width))) (PreH28 : (1 <= len)) (PreH29 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH30 : (2 <= len)) (PreH31 : ((0 : Int) <= left)) (PreH32 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left)) (PreH33 : ((left + len) <= total)) (PreH34 : (left <= split)) (PreH35 : (split <= ((left + len) - 1))) (PreH36 : ((0 : Int) <= best)) (PreH37 : (best <= 2100000000)) (PreH38 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best)) (PreH39 : ((Zlength (beads_l)) = n_pre)) (PreH40 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH41 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH42 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l_2)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l_2)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (total - len)) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ ((right + 1) < total) ” &&
  “ ((0 : Int) <= ((left * width) + right)) ” &&
  “ (((left * width) + right) < (total * width)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 2100000000) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (width = total) ” &&
  “ ((Zlength (vals_l)) = total) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (1 <= len) ” &&
  “ (EnergyLengthsComplete vals_l dp_l width len) ” &&
  “ (2 <= len) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (EnergyLeftComplete vals_l dp_l width len left) ” &&
  “ ((left + len) <= total) ” &&
  “ (left <= right) ” &&
  “ (right <= ((left + len) - 1)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 2100000000) ” &&
  “ (EnergySplitBest vals_l dp_l width len left right best) ” &&
  “ (EnergyIntervalBest vals_l left right best) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) beads_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) beads_l) ” &&
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
) \/
(
forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (split >= right)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < (total - len))) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : ((0 : Int) <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH24 : ((0 : Int) <= total)) (PreH25 : (width = total)) (PreH26 : ((Zlength (vals_l_2)) = total)) (PreH27 : ((Zlength (dp_l_2)) = (total * width))) (PreH28 : (1 <= len)) (PreH29 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH30 : (2 <= len)) (PreH31 : ((0 : Int) <= left)) (PreH32 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left)) (PreH33 : ((left + len) <= total)) (PreH34 : (left <= split)) (PreH35 : (split <= ((left + len) - 1))) (PreH36 : ((0 : Int) <= best)) (PreH37 : (best <= 2100000000)) (PreH38 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best)) (PreH39 : ((Zlength (beads_l)) = n_pre)) (PreH40 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH41 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH42 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  TT && emp 
|--
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ” &&
  “ (EnergyIntervalBest vals_l_2 left ((left + len) - 1) best) ” &&
  “ (EnergySplitBest vals_l_2 dp_l_2 width len left ((left + len) - 1) best) ” &&
  “ (((left * width) + ((left + len) - 1)) < ((2 * n_pre) * width)) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_14_split_goal_1 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (split >= right)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < (total - len))) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : ((0 : Int) <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH24 : ((0 : Int) <= total)) (PreH25 : (width = total)) (PreH26 : ((Zlength (vals_l_2)) = total)) (PreH27 : ((Zlength (dp_l_2)) = (total * width))) (PreH28 : (1 <= len)) (PreH29 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH30 : (2 <= len)) (PreH31 : ((0 : Int) <= left)) (PreH32 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left)) (PreH33 : ((left + len) <= total)) (PreH34 : (left <= split)) (PreH35 : (split <= ((left + len) - 1))) (PreH36 : ((0 : Int) <= best)) (PreH37 : (best <= 2100000000)) (PreH38 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best)) (PreH39 : ((Zlength (beads_l)) = n_pre)) (PreH40 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH41 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH42 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))

noncomputable def energyNecklace_entail_wit_14_split_goal_2 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (split >= right)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < (total - len))) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : ((0 : Int) <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH24 : ((0 : Int) <= total)) (PreH25 : (width = total)) (PreH26 : ((Zlength (vals_l_2)) = total)) (PreH27 : ((Zlength (dp_l_2)) = (total * width))) (PreH28 : (1 <= len)) (PreH29 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH30 : (2 <= len)) (PreH31 : ((0 : Int) <= left)) (PreH32 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left)) (PreH33 : ((left + len) <= total)) (PreH34 : (left <= split)) (PreH35 : (split <= ((left + len) - 1))) (PreH36 : ((0 : Int) <= best)) (PreH37 : (best <= 2100000000)) (PreH38 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best)) (PreH39 : ((Zlength (beads_l)) = n_pre)) (PreH40 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH41 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH42 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (EnergyIntervalBest vals_l_2 left ((left + len) - 1) best)

noncomputable def energyNecklace_entail_wit_14_split_goal_3 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (split >= right)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < (total - len))) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : ((0 : Int) <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH24 : ((0 : Int) <= total)) (PreH25 : (width = total)) (PreH26 : ((Zlength (vals_l_2)) = total)) (PreH27 : ((Zlength (dp_l_2)) = (total * width))) (PreH28 : (1 <= len)) (PreH29 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH30 : (2 <= len)) (PreH31 : ((0 : Int) <= left)) (PreH32 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left)) (PreH33 : ((left + len) <= total)) (PreH34 : (left <= split)) (PreH35 : (split <= ((left + len) - 1))) (PreH36 : ((0 : Int) <= best)) (PreH37 : (best <= 2100000000)) (PreH38 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best)) (PreH39 : ((Zlength (beads_l)) = n_pre)) (PreH40 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH41 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH42 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (EnergySplitBest vals_l_2 dp_l_2 width len left ((left + len) - 1) best)

noncomputable def energyNecklace_entail_wit_14_split_goal_4 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (split >= right)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left < (total - len))) (PreH12 : (right = ((left + len) - 1))) (PreH13 : (left < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : ((0 : Int) <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH24 : ((0 : Int) <= total)) (PreH25 : (width = total)) (PreH26 : ((Zlength (vals_l_2)) = total)) (PreH27 : ((Zlength (dp_l_2)) = (total * width))) (PreH28 : (1 <= len)) (PreH29 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH30 : (2 <= len)) (PreH31 : ((0 : Int) <= left)) (PreH32 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left)) (PreH33 : ((left + len) <= total)) (PreH34 : (left <= split)) (PreH35 : (split <= ((left + len) - 1))) (PreH36 : ((0 : Int) <= best)) (PreH37 : (best <= 2100000000)) (PreH38 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best)) (PreH39 : ((Zlength (beads_l)) = n_pre)) (PreH40 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH41 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH42 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (((left * width) + ((left + len) - 1)) < ((2 * n_pre) * width))

noncomputable def energyNecklace_entail_wit_15 : Prop :=
  (
forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : ((right + 1) < total)) (PreH13 : ((0 : Int) <= ((left * width) + right))) (PreH14 : (((left * width) + right) < (total * width))) (PreH15 : ((0 : Int) <= best)) (PreH16 : (best <= 2100000000)) (PreH17 : ((Zlength (beads_l)) = n_pre)) (PreH18 : ((Zlength (dp_l_2)) = (total * width))) (PreH19 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (width = total)) (PreH22 : ((Zlength (vals_l_2)) = total)) (PreH23 : ((Zlength (dp_l_2)) = (total * width))) (PreH24 : (1 <= len)) (PreH25 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH26 : (2 <= len)) (PreH27 : ((0 : Int) <= left)) (PreH28 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left)) (PreH29 : ((left + len) <= total)) (PreH30 : (left <= right)) (PreH31 : (right <= ((left + len) - 1))) (PreH32 : ((0 : Int) <= best)) (PreH33 : (best <= 2100000000)) (PreH34 : (EnergySplitBest vals_l_2 dp_l_2 width len left right best)) (PreH35 : (EnergyIntervalBest vals_l_2 left right best)) (PreH36 : ((Zlength (beads_l)) = n_pre)) (PreH37 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH39 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (intArray.full ( &( "dp" ) ) (total * width) (replace_Znth (((left * width) + right)) (best) (dp_l_2)))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l_2)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= (left + 1)) ” &&
  “ ((left + 1) <= (total - len)) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (width = total) ” &&
  “ ((Zlength (vals_l)) = total) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (1 <= len) ” &&
  “ (EnergyLengthsComplete vals_l dp_l width len) ” &&
  “ (2 <= len) ” &&
  “ ((0 : Int) <= (left + 1)) ” &&
  “ (EnergyLeftComplete vals_l dp_l width len (left + 1)) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) beads_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) beads_l) ” &&
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
) \/
(
forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : ((right + 1) < total)) (PreH13 : ((0 : Int) <= ((left * width) + right))) (PreH14 : (((left * width) + right) < (total * width))) (PreH15 : ((0 : Int) <= best)) (PreH16 : (best <= 2100000000)) (PreH17 : ((Zlength (beads_l)) = n_pre)) (PreH18 : ((Zlength (dp_l_2)) = (total * width))) (PreH19 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (width = total)) (PreH22 : ((Zlength (vals_l_2)) = total)) (PreH23 : ((Zlength (dp_l_2)) = (total * width))) (PreH24 : (1 <= len)) (PreH25 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH26 : (2 <= len)) (PreH27 : ((0 : Int) <= left)) (PreH28 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left)) (PreH29 : ((left + len) <= total)) (PreH30 : (left <= right)) (PreH31 : (right <= ((left + len) - 1))) (PreH32 : ((0 : Int) <= best)) (PreH33 : (best <= 2100000000)) (PreH34 : (EnergySplitBest vals_l_2 dp_l_2 width len left right best)) (PreH35 : (EnergyIntervalBest vals_l_2 left right best)) (PreH36 : ((Zlength (beads_l)) = n_pre)) (PreH37 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH39 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  TT && emp 
|--
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ” &&
  “ (EnergyLeftComplete vals_l_2 (replace_Znth (((left * total) + ((left + len) - 1))) (best) (dp_l_2)) total len (left + 1)) ” &&
  “ (EnergyLengthsComplete vals_l_2 (replace_Znth (((left * total) + ((left + len) - 1))) (best) (dp_l_2)) total len) ” &&
  “ ((Zlength ((replace_Znth (((left * total) + ((left + len) - 1))) (best) (dp_l_2)))) = ((2 * n_pre) * total)) ” &&
  “ ((Zlength ((replace_Znth (((left * total) + ((left + len) - 1))) (best) (dp_l_2)))) = ((2 * n_pre) * total)) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_15_split_goal_1 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : ((right + 1) < total)) (PreH13 : ((0 : Int) <= ((left * width) + right))) (PreH14 : (((left * width) + right) < (total * width))) (PreH15 : ((0 : Int) <= best)) (PreH16 : (best <= 2100000000)) (PreH17 : ((Zlength (beads_l)) = n_pre)) (PreH18 : ((Zlength (dp_l_2)) = (total * width))) (PreH19 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (width = total)) (PreH22 : ((Zlength (vals_l_2)) = total)) (PreH23 : ((Zlength (dp_l_2)) = (total * width))) (PreH24 : (1 <= len)) (PreH25 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH26 : (2 <= len)) (PreH27 : ((0 : Int) <= left)) (PreH28 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left)) (PreH29 : ((left + len) <= total)) (PreH30 : (left <= right)) (PreH31 : (right <= ((left + len) - 1))) (PreH32 : ((0 : Int) <= best)) (PreH33 : (best <= 2100000000)) (PreH34 : (EnergySplitBest vals_l_2 dp_l_2 width len left right best)) (PreH35 : (EnergyIntervalBest vals_l_2 left right best)) (PreH36 : ((Zlength (beads_l)) = n_pre)) (PreH37 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH39 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))

noncomputable def energyNecklace_entail_wit_15_split_goal_2 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : ((right + 1) < total)) (PreH13 : ((0 : Int) <= ((left * width) + right))) (PreH14 : (((left * width) + right) < (total * width))) (PreH15 : ((0 : Int) <= best)) (PreH16 : (best <= 2100000000)) (PreH17 : ((Zlength (beads_l)) = n_pre)) (PreH18 : ((Zlength (dp_l_2)) = (total * width))) (PreH19 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (width = total)) (PreH22 : ((Zlength (vals_l_2)) = total)) (PreH23 : ((Zlength (dp_l_2)) = (total * width))) (PreH24 : (1 <= len)) (PreH25 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH26 : (2 <= len)) (PreH27 : ((0 : Int) <= left)) (PreH28 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left)) (PreH29 : ((left + len) <= total)) (PreH30 : (left <= right)) (PreH31 : (right <= ((left + len) - 1))) (PreH32 : ((0 : Int) <= best)) (PreH33 : (best <= 2100000000)) (PreH34 : (EnergySplitBest vals_l_2 dp_l_2 width len left right best)) (PreH35 : (EnergyIntervalBest vals_l_2 left right best)) (PreH36 : ((Zlength (beads_l)) = n_pre)) (PreH37 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH39 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (EnergyLeftComplete vals_l_2 (replace_Znth (((left * total) + ((left + len) - 1))) (best) (dp_l_2)) total len (left + 1))

noncomputable def energyNecklace_entail_wit_15_split_goal_3 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : ((right + 1) < total)) (PreH13 : ((0 : Int) <= ((left * width) + right))) (PreH14 : (((left * width) + right) < (total * width))) (PreH15 : ((0 : Int) <= best)) (PreH16 : (best <= 2100000000)) (PreH17 : ((Zlength (beads_l)) = n_pre)) (PreH18 : ((Zlength (dp_l_2)) = (total * width))) (PreH19 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (width = total)) (PreH22 : ((Zlength (vals_l_2)) = total)) (PreH23 : ((Zlength (dp_l_2)) = (total * width))) (PreH24 : (1 <= len)) (PreH25 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH26 : (2 <= len)) (PreH27 : ((0 : Int) <= left)) (PreH28 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left)) (PreH29 : ((left + len) <= total)) (PreH30 : (left <= right)) (PreH31 : (right <= ((left + len) - 1))) (PreH32 : ((0 : Int) <= best)) (PreH33 : (best <= 2100000000)) (PreH34 : (EnergySplitBest vals_l_2 dp_l_2 width len left right best)) (PreH35 : (EnergyIntervalBest vals_l_2 left right best)) (PreH36 : ((Zlength (beads_l)) = n_pre)) (PreH37 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH39 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (EnergyLengthsComplete vals_l_2 (replace_Znth (((left * total) + ((left + len) - 1))) (best) (dp_l_2)) total len)

noncomputable def energyNecklace_entail_wit_15_split_goal_4 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : ((right + 1) < total)) (PreH13 : ((0 : Int) <= ((left * width) + right))) (PreH14 : (((left * width) + right) < (total * width))) (PreH15 : ((0 : Int) <= best)) (PreH16 : (best <= 2100000000)) (PreH17 : ((Zlength (beads_l)) = n_pre)) (PreH18 : ((Zlength (dp_l_2)) = (total * width))) (PreH19 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (width = total)) (PreH22 : ((Zlength (vals_l_2)) = total)) (PreH23 : ((Zlength (dp_l_2)) = (total * width))) (PreH24 : (1 <= len)) (PreH25 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH26 : (2 <= len)) (PreH27 : ((0 : Int) <= left)) (PreH28 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left)) (PreH29 : ((left + len) <= total)) (PreH30 : (left <= right)) (PreH31 : (right <= ((left + len) - 1))) (PreH32 : ((0 : Int) <= best)) (PreH33 : (best <= 2100000000)) (PreH34 : (EnergySplitBest vals_l_2 dp_l_2 width len left right best)) (PreH35 : (EnergyIntervalBest vals_l_2 left right best)) (PreH36 : ((Zlength (beads_l)) = n_pre)) (PreH37 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH39 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  ((Zlength ((replace_Znth (((left * total) + ((left + len) - 1))) (best) (dp_l_2)))) = ((2 * n_pre) * total))

noncomputable def energyNecklace_entail_wit_15_split_goal_5 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : ((right + 1) < total)) (PreH13 : ((0 : Int) <= ((left * width) + right))) (PreH14 : (((left * width) + right) < (total * width))) (PreH15 : ((0 : Int) <= best)) (PreH16 : (best <= 2100000000)) (PreH17 : ((Zlength (beads_l)) = n_pre)) (PreH18 : ((Zlength (dp_l_2)) = (total * width))) (PreH19 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (width = total)) (PreH22 : ((Zlength (vals_l_2)) = total)) (PreH23 : ((Zlength (dp_l_2)) = (total * width))) (PreH24 : (1 <= len)) (PreH25 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH26 : (2 <= len)) (PreH27 : ((0 : Int) <= left)) (PreH28 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left)) (PreH29 : ((left + len) <= total)) (PreH30 : (left <= right)) (PreH31 : (right <= ((left + len) - 1))) (PreH32 : ((0 : Int) <= best)) (PreH33 : (best <= 2100000000)) (PreH34 : (EnergySplitBest vals_l_2 dp_l_2 width len left right best)) (PreH35 : (EnergyIntervalBest vals_l_2 left right best)) (PreH36 : ((Zlength (beads_l)) = n_pre)) (PreH37 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH39 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  ((Zlength ((replace_Znth (((left * total) + ((left + len) - 1))) (best) (dp_l_2)))) = ((2 * n_pre) * total))

noncomputable def energyNecklace_entail_wit_16 : Prop :=
  (
forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (left >= (total - len))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= (total - len))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l_2)) = total)) (PreH18 : ((Zlength (dp_l_2)) = (total * width))) (PreH19 : (1 <= len)) (PreH20 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH21 : (2 <= len)) (PreH22 : ((0 : Int) <= left)) (PreH23 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH26 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH27 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l_2)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l_2)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ (2 <= (len + 1)) ” &&
  “ ((len + 1) <= (n_pre + 1)) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (width = total) ” &&
  “ ((Zlength (vals_l)) = total) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (1 <= (len + 1)) ” &&
  “ (EnergyLengthsComplete vals_l dp_l width (len + 1)) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) beads_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) beads_l) ” &&
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
) \/
(
forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (left >= (total - len))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= (total - len))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l_2)) = total)) (PreH18 : ((Zlength (dp_l_2)) = (total * width))) (PreH19 : (1 <= len)) (PreH20 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH21 : (2 <= len)) (PreH22 : ((0 : Int) <= left)) (PreH23 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH26 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH27 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  TT && emp 
|--
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ” &&
  “ (EnergyLengthsComplete vals_l_2 dp_l_2 width (len + 1)) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_16_split_goal_1 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (left >= (total - len))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= (total - len))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l_2)) = total)) (PreH18 : ((Zlength (dp_l_2)) = (total * width))) (PreH19 : (1 <= len)) (PreH20 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH21 : (2 <= len)) (PreH22 : ((0 : Int) <= left)) (PreH23 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH26 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH27 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))

noncomputable def energyNecklace_entail_wit_16_split_goal_2 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (left : Int) (len : Int) (width : Int) (total : Int) (PreH1 : (left >= (total - len))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : ((0 : Int) <= left)) (PreH11 : (left <= (total - len))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l_2)) = total)) (PreH18 : ((Zlength (dp_l_2)) = (total * width))) (PreH19 : (1 <= len)) (PreH20 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH21 : (2 <= len)) (PreH22 : ((0 : Int) <= left)) (PreH23 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH26 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH27 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (EnergyLengthsComplete vals_l_2 dp_l_2 width (len + 1))

noncomputable def energyNecklace_entail_wit_17 : Prop :=
  (
forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (len : Int) (width : Int) (total : Int) (PreH1 : (len > n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l_2)) = (total * width))) (PreH12 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (width = total)) (PreH15 : ((Zlength (vals_l_2)) = total)) (PreH16 : ((Zlength (dp_l_2)) = (total * width))) (PreH17 : (1 <= len)) (PreH18 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH19 : ((Zlength (beads_l)) = n_pre)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH22 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l_2)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l_2)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 2100000000) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (width = total) ” &&
  “ ((Zlength (vals_l)) = total) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (1 <= (n_pre + 1)) ” &&
  “ (EnergyLengthsComplete vals_l dp_l width (n_pre + 1)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (width = total) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 2100000000) ” &&
  “ (EnergyAnswerBest vals_l n_pre (0 : Int) (0 : Int)) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) beads_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) beads_l) ” &&
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
) \/
(
forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (len : Int) (width : Int) (total : Int) (PreH1 : (len > n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l_2)) = (total * width))) (PreH12 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (width = total)) (PreH15 : ((Zlength (vals_l_2)) = total)) (PreH16 : ((Zlength (dp_l_2)) = (total * width))) (PreH17 : (1 <= len)) (PreH18 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH19 : ((Zlength (beads_l)) = n_pre)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH22 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  TT && emp 
|--
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ” &&
  “ (EnergyAnswerBest vals_l_2 n_pre (0 : Int) (0 : Int)) ” &&
  “ (EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1)) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_17_split_goal_1 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (len : Int) (width : Int) (total : Int) (PreH1 : (len > n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l_2)) = (total * width))) (PreH12 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (width = total)) (PreH15 : ((Zlength (vals_l_2)) = total)) (PreH16 : ((Zlength (dp_l_2)) = (total * width))) (PreH17 : (1 <= len)) (PreH18 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH19 : ((Zlength (beads_l)) = n_pre)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH22 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))

noncomputable def energyNecklace_entail_wit_17_split_goal_2 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (len : Int) (width : Int) (total : Int) (PreH1 : (len > n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l_2)) = (total * width))) (PreH12 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (width = total)) (PreH15 : ((Zlength (vals_l_2)) = total)) (PreH16 : ((Zlength (dp_l_2)) = (total * width))) (PreH17 : (1 <= len)) (PreH18 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH19 : ((Zlength (beads_l)) = n_pre)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH22 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (EnergyAnswerBest vals_l_2 n_pre (0 : Int) (0 : Int))

noncomputable def energyNecklace_entail_wit_17_split_goal_3 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (len : Int) (width : Int) (total : Int) (PreH1 : (len > n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l_2)) = (total * width))) (PreH12 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (width = total)) (PreH15 : ((Zlength (vals_l_2)) = total)) (PreH16 : ((Zlength (dp_l_2)) = (total * width))) (PreH17 : (1 <= len)) (PreH18 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len)) (PreH19 : ((Zlength (beads_l)) = n_pre)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH22 : forall (ev_2 : (List Int)) , forall (start_2 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1))

noncomputable def energyNecklace_entail_wit_18 : Prop :=
  (
forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (answer : Int) (start : Int) (width : Int) (total : Int) (PreH1 : (start < n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((0 : Int) <= start)) (PreH9 : (start <= n_pre)) (PreH10 : ((0 : Int) <= answer)) (PreH11 : (answer <= 2100000000)) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l_2)) = total)) (PreH18 : ((Zlength (dp_l_2)) = (total * width))) (PreH19 : (1 <= (n_pre + 1))) (PreH20 : (EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1))) (PreH21 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width))) (PreH23 : (width = total)) (PreH24 : ((0 : Int) <= start)) (PreH25 : (start <= n_pre)) (PreH26 : ((0 : Int) <= answer)) (PreH27 : (answer <= 2100000000)) (PreH28 : (EnergyAnswerBest vals_l_2 n_pre start answer)) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH31 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH32 : forall (ev_2 : (List Int)) , forall (start_3 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_3)) ∧ (start_3 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l_2)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l_2)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((0 : Int) <= start) ” &&
  “ (start < n_pre) ” &&
  “ ((0 : Int) <= ((((start * width) + start) + n_pre) - 1)) ” &&
  “ (((((start * width) + start) + n_pre) - 1) < (total * width)) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (width = total) ” &&
  “ ((Zlength (vals_l)) = total) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (1 <= (n_pre + 1)) ” &&
  “ (EnergyLengthsComplete vals_l dp_l width (n_pre + 1)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (width = total) ” &&
  “ ((0 : Int) <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 2100000000) ” &&
  “ (EnergyAnswerBest vals_l n_pre start answer) ” &&
  “ (EnergyIntervalBest vals_l start ((start + n_pre) - 1) (Znth ((((start * width) + start) + n_pre) - 1) dp_l (0 : Int))) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) beads_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) beads_l) ” &&
  “ forall (ev : (List Int)) , forall (start_2 : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev start_2 ((start_2 + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
) \/
(
forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (answer : Int) (start : Int) (width : Int) (total : Int) (PreH1 : (start < n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((0 : Int) <= start)) (PreH9 : (start <= n_pre)) (PreH10 : ((0 : Int) <= answer)) (PreH11 : (answer <= 2100000000)) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l_2)) = total)) (PreH18 : ((Zlength (dp_l_2)) = (total * width))) (PreH19 : (1 <= (n_pre + 1))) (PreH20 : (EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1))) (PreH21 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width))) (PreH23 : (width = total)) (PreH24 : ((0 : Int) <= start)) (PreH25 : (start <= n_pre)) (PreH26 : ((0 : Int) <= answer)) (PreH27 : (answer <= 2100000000)) (PreH28 : (EnergyAnswerBest vals_l_2 n_pre start answer)) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH31 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH32 : forall (ev_2 : (List Int)) , forall (start_3 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_3)) ∧ (start_3 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  TT && emp 
|--
  “ forall (ev : (List Int)) , forall (start_2 : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev start_2 ((start_2 + n_pre) - 1) energy)) -> (energy <= 2100000000)) ” &&
  “ (EnergyIntervalBest vals_l_2 start ((start + n_pre) - 1) (Znth ((((start * width) + start) + n_pre) - 1) dp_l_2 (0 : Int))) ” &&
  “ (((((start * width) + start) + n_pre) - 1) < ((2 * n_pre) * width)) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_18_split_goal_1 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (answer : Int) (start : Int) (width : Int) (total : Int) (PreH1 : (start < n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((0 : Int) <= start)) (PreH9 : (start <= n_pre)) (PreH10 : ((0 : Int) <= answer)) (PreH11 : (answer <= 2100000000)) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l_2)) = total)) (PreH18 : ((Zlength (dp_l_2)) = (total * width))) (PreH19 : (1 <= (n_pre + 1))) (PreH20 : (EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1))) (PreH21 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width))) (PreH23 : (width = total)) (PreH24 : ((0 : Int) <= start)) (PreH25 : (start <= n_pre)) (PreH26 : ((0 : Int) <= answer)) (PreH27 : (answer <= 2100000000)) (PreH28 : (EnergyAnswerBest vals_l_2 n_pre start answer)) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH31 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH32 : forall (ev_2 : (List Int)) , forall (start_3 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_3)) ∧ (start_3 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  forall (ev : (List Int)) , forall (start_2 : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev start_2 ((start_2 + n_pre) - 1) energy)) -> (energy <= 2100000000))

noncomputable def energyNecklace_entail_wit_18_split_goal_2 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (answer : Int) (start : Int) (width : Int) (total : Int) (PreH1 : (start < n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((0 : Int) <= start)) (PreH9 : (start <= n_pre)) (PreH10 : ((0 : Int) <= answer)) (PreH11 : (answer <= 2100000000)) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l_2)) = total)) (PreH18 : ((Zlength (dp_l_2)) = (total * width))) (PreH19 : (1 <= (n_pre + 1))) (PreH20 : (EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1))) (PreH21 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width))) (PreH23 : (width = total)) (PreH24 : ((0 : Int) <= start)) (PreH25 : (start <= n_pre)) (PreH26 : ((0 : Int) <= answer)) (PreH27 : (answer <= 2100000000)) (PreH28 : (EnergyAnswerBest vals_l_2 n_pre start answer)) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH31 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH32 : forall (ev_2 : (List Int)) , forall (start_3 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_3)) ∧ (start_3 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (EnergyIntervalBest vals_l_2 start ((start + n_pre) - 1) (Znth ((((start * width) + start) + n_pre) - 1) dp_l_2 (0 : Int)))

noncomputable def energyNecklace_entail_wit_18_split_goal_3 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (answer : Int) (start : Int) (width : Int) (total : Int) (PreH1 : (start < n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((0 : Int) <= start)) (PreH9 : (start <= n_pre)) (PreH10 : ((0 : Int) <= answer)) (PreH11 : (answer <= 2100000000)) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l_2)) = total)) (PreH18 : ((Zlength (dp_l_2)) = (total * width))) (PreH19 : (1 <= (n_pre + 1))) (PreH20 : (EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1))) (PreH21 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width))) (PreH23 : (width = total)) (PreH24 : ((0 : Int) <= start)) (PreH25 : (start <= n_pre)) (PreH26 : ((0 : Int) <= answer)) (PreH27 : (answer <= 2100000000)) (PreH28 : (EnergyAnswerBest vals_l_2 n_pre start answer)) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH31 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH32 : forall (ev_2 : (List Int)) , forall (start_3 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_3)) ∧ (start_3 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (((((start * width) + start) + n_pre) - 1) < ((2 * n_pre) * width))

noncomputable def energyNecklace_entail_wit_19 : Prop :=
  (
forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (start : Int) (answer : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start < n_pre)) (PreH9 : ((0 : Int) <= ((((start * width) + start) + n_pre) - 1))) (PreH10 : (((((start * width) + start) + n_pre) - 1) < (total * width))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width))) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH14 : ((0 : Int) <= total)) (PreH15 : (width = total)) (PreH16 : ((Zlength (vals_l_2)) = total)) (PreH17 : ((Zlength (dp_l)) = (total * width))) (PreH18 : (1 <= (n_pre + 1))) (PreH19 : (EnergyLengthsComplete vals_l_2 dp_l width (n_pre + 1))) (PreH20 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH21 : ((Zlength (dp_l)) = (total * width))) (PreH22 : (width = total)) (PreH23 : ((0 : Int) <= start)) (PreH24 : (start <= n_pre)) (PreH25 : ((0 : Int) <= answer)) (PreH26 : (answer <= 2100000000)) (PreH27 : (EnergyAnswerBest vals_l_2 n_pre start answer)) (PreH28 : (EnergyIntervalBest vals_l_2 start ((start + n_pre) - 1) (Znth ((((start * width) + start) + n_pre) - 1) dp_l (0 : Int)))) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH31 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH32 : forall (ev_2 : (List Int)) , forall (start_3 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_3)) ∧ (start_3 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l_2)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  EX vals_l : (List Int), EX dp_l_2 : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((0 : Int) <= start) ” &&
  “ (start < n_pre) ” &&
  “ ((Znth ((((start * width) + start) + n_pre) - 1) dp_l (0 : Int)) = (Znth ((((start * width) + start) + n_pre) - 1) dp_l_2 (0 : Int))) ” &&
  “ ((0 : Int) <= (Znth ((((start * width) + start) + n_pre) - 1) dp_l (0 : Int))) ” &&
  “ ((Znth ((((start * width) + start) + n_pre) - 1) dp_l (0 : Int)) <= 2100000000) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l_2)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (width = total) ” &&
  “ ((Zlength (vals_l)) = total) ” &&
  “ ((Zlength (dp_l_2)) = (total * width)) ” &&
  “ (1 <= (n_pre + 1)) ” &&
  “ (EnergyLengthsComplete vals_l dp_l_2 width (n_pre + 1)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ ((Zlength (dp_l_2)) = (total * width)) ” &&
  “ (width = total) ” &&
  “ ((0 : Int) <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 2100000000) ” &&
  “ (EnergyAnswerBest vals_l n_pre start answer) ” &&
  “ (EnergyIntervalBest vals_l start ((start + n_pre) - 1) (Znth ((((start * width) + start) + n_pre) - 1) dp_l (0 : Int))) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) beads_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) beads_l) ” &&
  “ forall (ev : (List Int)) , forall (start_2 : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev start_2 ((start_2 + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l_2)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
) \/
(
forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (start : Int) (answer : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start < n_pre)) (PreH9 : ((0 : Int) <= ((((start * width) + start) + n_pre) - 1))) (PreH10 : (((((start * width) + start) + n_pre) - 1) < (total * width))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width))) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH14 : ((0 : Int) <= total)) (PreH15 : (width = total)) (PreH16 : ((Zlength (vals_l_2)) = total)) (PreH17 : ((Zlength (dp_l)) = (total * width))) (PreH18 : (1 <= (n_pre + 1))) (PreH19 : (EnergyLengthsComplete vals_l_2 dp_l width (n_pre + 1))) (PreH20 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH21 : ((Zlength (dp_l)) = (total * width))) (PreH22 : (width = total)) (PreH23 : ((0 : Int) <= start)) (PreH24 : (start <= n_pre)) (PreH25 : ((0 : Int) <= answer)) (PreH26 : (answer <= 2100000000)) (PreH27 : (EnergyAnswerBest vals_l_2 n_pre start answer)) (PreH28 : (EnergyIntervalBest vals_l_2 start ((start + n_pre) - 1) (Znth ((((start * width) + start) + n_pre) - 1) dp_l (0 : Int)))) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH31 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH32 : forall (ev_2 : (List Int)) , forall (start_3 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_3)) ∧ (start_3 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  TT && emp 
|--
  “ forall (ev : (List Int)) , forall (start_2 : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev start_2 ((start_2 + n_pre) - 1) energy)) -> (energy <= 2100000000)) ” &&
  “ ((Znth ((((start * total) + start) + n_pre) - 1) dp_l (0 : Int)) <= 2100000000) ” &&
  “ ((0 : Int) <= (Znth ((((start * total) + start) + n_pre) - 1) dp_l (0 : Int))) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_19_split_goal_1 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (start : Int) (answer : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start < n_pre)) (PreH9 : ((0 : Int) <= ((((start * width) + start) + n_pre) - 1))) (PreH10 : (((((start * width) + start) + n_pre) - 1) < (total * width))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width))) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH14 : ((0 : Int) <= total)) (PreH15 : (width = total)) (PreH16 : ((Zlength (vals_l_2)) = total)) (PreH17 : ((Zlength (dp_l)) = (total * width))) (PreH18 : (1 <= (n_pre + 1))) (PreH19 : (EnergyLengthsComplete vals_l_2 dp_l width (n_pre + 1))) (PreH20 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH21 : ((Zlength (dp_l)) = (total * width))) (PreH22 : (width = total)) (PreH23 : ((0 : Int) <= start)) (PreH24 : (start <= n_pre)) (PreH25 : ((0 : Int) <= answer)) (PreH26 : (answer <= 2100000000)) (PreH27 : (EnergyAnswerBest vals_l_2 n_pre start answer)) (PreH28 : (EnergyIntervalBest vals_l_2 start ((start + n_pre) - 1) (Znth ((((start * width) + start) + n_pre) - 1) dp_l (0 : Int)))) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH31 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH32 : forall (ev_2 : (List Int)) , forall (start_3 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_3)) ∧ (start_3 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  forall (ev : (List Int)) , forall (start_2 : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev start_2 ((start_2 + n_pre) - 1) energy)) -> (energy <= 2100000000))

noncomputable def energyNecklace_entail_wit_19_split_goal_2 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (start : Int) (answer : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start < n_pre)) (PreH9 : ((0 : Int) <= ((((start * width) + start) + n_pre) - 1))) (PreH10 : (((((start * width) + start) + n_pre) - 1) < (total * width))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width))) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH14 : ((0 : Int) <= total)) (PreH15 : (width = total)) (PreH16 : ((Zlength (vals_l_2)) = total)) (PreH17 : ((Zlength (dp_l)) = (total * width))) (PreH18 : (1 <= (n_pre + 1))) (PreH19 : (EnergyLengthsComplete vals_l_2 dp_l width (n_pre + 1))) (PreH20 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH21 : ((Zlength (dp_l)) = (total * width))) (PreH22 : (width = total)) (PreH23 : ((0 : Int) <= start)) (PreH24 : (start <= n_pre)) (PreH25 : ((0 : Int) <= answer)) (PreH26 : (answer <= 2100000000)) (PreH27 : (EnergyAnswerBest vals_l_2 n_pre start answer)) (PreH28 : (EnergyIntervalBest vals_l_2 start ((start + n_pre) - 1) (Znth ((((start * width) + start) + n_pre) - 1) dp_l (0 : Int)))) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH31 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH32 : forall (ev_2 : (List Int)) , forall (start_3 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_3)) ∧ (start_3 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  ((Znth ((((start * total) + start) + n_pre) - 1) dp_l (0 : Int)) <= 2100000000)

noncomputable def energyNecklace_entail_wit_19_split_goal_3 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (start : Int) (answer : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((0 : Int) <= start)) (PreH8 : (start < n_pre)) (PreH9 : ((0 : Int) <= ((((start * width) + start) + n_pre) - 1))) (PreH10 : (((((start * width) + start) + n_pre) - 1) < (total * width))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width))) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH14 : ((0 : Int) <= total)) (PreH15 : (width = total)) (PreH16 : ((Zlength (vals_l_2)) = total)) (PreH17 : ((Zlength (dp_l)) = (total * width))) (PreH18 : (1 <= (n_pre + 1))) (PreH19 : (EnergyLengthsComplete vals_l_2 dp_l width (n_pre + 1))) (PreH20 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH21 : ((Zlength (dp_l)) = (total * width))) (PreH22 : (width = total)) (PreH23 : ((0 : Int) <= start)) (PreH24 : (start <= n_pre)) (PreH25 : ((0 : Int) <= answer)) (PreH26 : (answer <= 2100000000)) (PreH27 : (EnergyAnswerBest vals_l_2 n_pre start answer)) (PreH28 : (EnergyIntervalBest vals_l_2 start ((start + n_pre) - 1) (Znth ((((start * width) + start) + n_pre) - 1) dp_l (0 : Int)))) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH31 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH32 : forall (ev_2 : (List Int)) , forall (start_3 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_3)) ∧ (start_3 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  ((0 : Int) <= (Znth ((((start * total) + start) + n_pre) - 1) dp_l (0 : Int)))

noncomputable def energyNecklace_entail_wit_20_1 : Prop :=
  (
forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (start : Int) (value : Int) (answer : Int) (PreH1 : (value > answer)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((0 : Int) <= start)) (PreH9 : (start < n_pre)) (PreH10 : (value = (Znth ((((start * width) + start) + n_pre) - 1) dp_l_2 (0 : Int)))) (PreH11 : ((0 : Int) <= value)) (PreH12 : (value <= 2100000000)) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : ((Zlength (dp_l_2)) = (total * width))) (PreH15 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH16 : ((0 : Int) <= total)) (PreH17 : (width = total)) (PreH18 : ((Zlength (vals_l_2)) = total)) (PreH19 : ((Zlength (dp_l_2)) = (total * width))) (PreH20 : (1 <= (n_pre + 1))) (PreH21 : (EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1))) (PreH22 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH23 : ((Zlength (dp_l_2)) = (total * width))) (PreH24 : (width = total)) (PreH25 : ((0 : Int) <= start)) (PreH26 : (start <= n_pre)) (PreH27 : ((0 : Int) <= answer)) (PreH28 : (answer <= 2100000000)) (PreH29 : (EnergyAnswerBest vals_l_2 n_pre start answer)) (PreH30 : (EnergyIntervalBest vals_l_2 start ((start + n_pre) - 1) value)) (PreH31 : ((Zlength (beads_l)) = n_pre)) (PreH32 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH33 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH34 : forall (ev_2 : (List Int)) , forall (start_3 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_3)) ∧ (start_3 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l_2)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l_2)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((0 : Int) <= start) ” &&
  “ (start < n_pre) ” &&
  “ (value = (Znth ((((start * width) + start) + n_pre) - 1) dp_l (0 : Int))) ” &&
  “ ((0 : Int) <= value) ” &&
  “ (value <= 2100000000) ” &&
  “ ((0 : Int) <= value) ” &&
  “ (value <= 2100000000) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (width = total) ” &&
  “ ((Zlength (vals_l)) = total) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (1 <= (n_pre + 1)) ” &&
  “ (EnergyLengthsComplete vals_l dp_l width (n_pre + 1)) ” &&
  “ (EnergyIntervalBest vals_l start ((start + n_pre) - 1) value) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (width = total) ” &&
  “ ((0 : Int) <= (start + 1)) ” &&
  “ ((start + 1) <= n_pre) ” &&
  “ ((0 : Int) <= value) ” &&
  “ (value <= 2100000000) ” &&
  “ (EnergyAnswerBest vals_l n_pre (start + 1) value) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) beads_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) beads_l) ” &&
  “ forall (ev : (List Int)) , forall (start_2 : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev start_2 ((start_2 + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
) \/
(
forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (start : Int) (value : Int) (answer : Int) (PreH1 : (value > answer)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((0 : Int) <= start)) (PreH9 : (start < n_pre)) (PreH10 : (value = (Znth ((((start * width) + start) + n_pre) - 1) dp_l_2 (0 : Int)))) (PreH11 : ((0 : Int) <= value)) (PreH12 : (value <= 2100000000)) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : ((Zlength (dp_l_2)) = (total * width))) (PreH15 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH16 : ((0 : Int) <= total)) (PreH17 : (width = total)) (PreH18 : ((Zlength (vals_l_2)) = total)) (PreH19 : ((Zlength (dp_l_2)) = (total * width))) (PreH20 : (1 <= (n_pre + 1))) (PreH21 : (EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1))) (PreH22 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH23 : ((Zlength (dp_l_2)) = (total * width))) (PreH24 : (width = total)) (PreH25 : ((0 : Int) <= start)) (PreH26 : (start <= n_pre)) (PreH27 : ((0 : Int) <= answer)) (PreH28 : (answer <= 2100000000)) (PreH29 : (EnergyAnswerBest vals_l_2 n_pre start answer)) (PreH30 : (EnergyIntervalBest vals_l_2 start ((start + n_pre) - 1) value)) (PreH31 : ((Zlength (beads_l)) = n_pre)) (PreH32 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH33 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH34 : forall (ev_2 : (List Int)) , forall (start_3 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_3)) ∧ (start_3 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  TT && emp 
|--
  “ forall (ev : (List Int)) , forall (start_2 : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev start_2 ((start_2 + n_pre) - 1) energy)) -> (energy <= 2100000000)) ” &&
  “ (EnergyAnswerBest vals_l_2 n_pre (start + 1) value) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_20_1_split_goal_1 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (start : Int) (value : Int) (answer : Int) (PreH1 : (value > answer)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((0 : Int) <= start)) (PreH9 : (start < n_pre)) (PreH10 : (value = (Znth ((((start * width) + start) + n_pre) - 1) dp_l_2 (0 : Int)))) (PreH11 : ((0 : Int) <= value)) (PreH12 : (value <= 2100000000)) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : ((Zlength (dp_l_2)) = (total * width))) (PreH15 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH16 : ((0 : Int) <= total)) (PreH17 : (width = total)) (PreH18 : ((Zlength (vals_l_2)) = total)) (PreH19 : ((Zlength (dp_l_2)) = (total * width))) (PreH20 : (1 <= (n_pre + 1))) (PreH21 : (EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1))) (PreH22 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH23 : ((Zlength (dp_l_2)) = (total * width))) (PreH24 : (width = total)) (PreH25 : ((0 : Int) <= start)) (PreH26 : (start <= n_pre)) (PreH27 : ((0 : Int) <= answer)) (PreH28 : (answer <= 2100000000)) (PreH29 : (EnergyAnswerBest vals_l_2 n_pre start answer)) (PreH30 : (EnergyIntervalBest vals_l_2 start ((start + n_pre) - 1) value)) (PreH31 : ((Zlength (beads_l)) = n_pre)) (PreH32 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH33 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH34 : forall (ev_2 : (List Int)) , forall (start_3 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_3)) ∧ (start_3 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  forall (ev : (List Int)) , forall (start_2 : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev start_2 ((start_2 + n_pre) - 1) energy)) -> (energy <= 2100000000))

noncomputable def energyNecklace_entail_wit_20_1_split_goal_2 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (start : Int) (value : Int) (answer : Int) (PreH1 : (value > answer)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((0 : Int) <= start)) (PreH9 : (start < n_pre)) (PreH10 : (value = (Znth ((((start * width) + start) + n_pre) - 1) dp_l_2 (0 : Int)))) (PreH11 : ((0 : Int) <= value)) (PreH12 : (value <= 2100000000)) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : ((Zlength (dp_l_2)) = (total * width))) (PreH15 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH16 : ((0 : Int) <= total)) (PreH17 : (width = total)) (PreH18 : ((Zlength (vals_l_2)) = total)) (PreH19 : ((Zlength (dp_l_2)) = (total * width))) (PreH20 : (1 <= (n_pre + 1))) (PreH21 : (EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1))) (PreH22 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH23 : ((Zlength (dp_l_2)) = (total * width))) (PreH24 : (width = total)) (PreH25 : ((0 : Int) <= start)) (PreH26 : (start <= n_pre)) (PreH27 : ((0 : Int) <= answer)) (PreH28 : (answer <= 2100000000)) (PreH29 : (EnergyAnswerBest vals_l_2 n_pre start answer)) (PreH30 : (EnergyIntervalBest vals_l_2 start ((start + n_pre) - 1) value)) (PreH31 : ((Zlength (beads_l)) = n_pre)) (PreH32 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH33 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH34 : forall (ev_2 : (List Int)) , forall (start_3 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_3)) ∧ (start_3 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (EnergyAnswerBest vals_l_2 n_pre (start + 1) value)

noncomputable def energyNecklace_entail_wit_20_2 : Prop :=
  (
forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (start : Int) (value : Int) (answer : Int) (PreH1 : (value <= answer)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((0 : Int) <= start)) (PreH9 : (start < n_pre)) (PreH10 : (value = (Znth ((((start * width) + start) + n_pre) - 1) dp_l_2 (0 : Int)))) (PreH11 : ((0 : Int) <= value)) (PreH12 : (value <= 2100000000)) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : ((Zlength (dp_l_2)) = (total * width))) (PreH15 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH16 : ((0 : Int) <= total)) (PreH17 : (width = total)) (PreH18 : ((Zlength (vals_l_2)) = total)) (PreH19 : ((Zlength (dp_l_2)) = (total * width))) (PreH20 : (1 <= (n_pre + 1))) (PreH21 : (EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1))) (PreH22 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH23 : ((Zlength (dp_l_2)) = (total * width))) (PreH24 : (width = total)) (PreH25 : ((0 : Int) <= start)) (PreH26 : (start <= n_pre)) (PreH27 : ((0 : Int) <= answer)) (PreH28 : (answer <= 2100000000)) (PreH29 : (EnergyAnswerBest vals_l_2 n_pre start answer)) (PreH30 : (EnergyIntervalBest vals_l_2 start ((start + n_pre) - 1) value)) (PreH31 : ((Zlength (beads_l)) = n_pre)) (PreH32 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH33 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH34 : forall (ev_2 : (List Int)) , forall (start_3 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_3)) ∧ (start_3 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l_2)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l_2)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((0 : Int) <= start) ” &&
  “ (start < n_pre) ” &&
  “ (value = (Znth ((((start * width) + start) + n_pre) - 1) dp_l (0 : Int))) ” &&
  “ ((0 : Int) <= value) ” &&
  “ (value <= 2100000000) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 2100000000) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (width = total) ” &&
  “ ((Zlength (vals_l)) = total) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (1 <= (n_pre + 1)) ” &&
  “ (EnergyLengthsComplete vals_l dp_l width (n_pre + 1)) ” &&
  “ (EnergyIntervalBest vals_l start ((start + n_pre) - 1) value) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (width = total) ” &&
  “ ((0 : Int) <= (start + 1)) ” &&
  “ ((start + 1) <= n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 2100000000) ” &&
  “ (EnergyAnswerBest vals_l n_pre (start + 1) answer) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) beads_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) beads_l) ” &&
  “ forall (ev : (List Int)) , forall (start_2 : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev start_2 ((start_2 + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
) \/
(
forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (start : Int) (value : Int) (answer : Int) (PreH1 : (value <= answer)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((0 : Int) <= start)) (PreH9 : (start < n_pre)) (PreH10 : (value = (Znth ((((start * width) + start) + n_pre) - 1) dp_l_2 (0 : Int)))) (PreH11 : ((0 : Int) <= value)) (PreH12 : (value <= 2100000000)) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : ((Zlength (dp_l_2)) = (total * width))) (PreH15 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH16 : ((0 : Int) <= total)) (PreH17 : (width = total)) (PreH18 : ((Zlength (vals_l_2)) = total)) (PreH19 : ((Zlength (dp_l_2)) = (total * width))) (PreH20 : (1 <= (n_pre + 1))) (PreH21 : (EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1))) (PreH22 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH23 : ((Zlength (dp_l_2)) = (total * width))) (PreH24 : (width = total)) (PreH25 : ((0 : Int) <= start)) (PreH26 : (start <= n_pre)) (PreH27 : ((0 : Int) <= answer)) (PreH28 : (answer <= 2100000000)) (PreH29 : (EnergyAnswerBest vals_l_2 n_pre start answer)) (PreH30 : (EnergyIntervalBest vals_l_2 start ((start + n_pre) - 1) value)) (PreH31 : ((Zlength (beads_l)) = n_pre)) (PreH32 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH33 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH34 : forall (ev_2 : (List Int)) , forall (start_3 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_3)) ∧ (start_3 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  TT && emp 
|--
  “ forall (ev : (List Int)) , forall (start_2 : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev start_2 ((start_2 + n_pre) - 1) energy)) -> (energy <= 2100000000)) ” &&
  “ (EnergyAnswerBest vals_l_2 n_pre (start + 1) answer) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_20_2_split_goal_1 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (start : Int) (value : Int) (answer : Int) (PreH1 : (value <= answer)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((0 : Int) <= start)) (PreH9 : (start < n_pre)) (PreH10 : (value = (Znth ((((start * width) + start) + n_pre) - 1) dp_l_2 (0 : Int)))) (PreH11 : ((0 : Int) <= value)) (PreH12 : (value <= 2100000000)) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : ((Zlength (dp_l_2)) = (total * width))) (PreH15 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH16 : ((0 : Int) <= total)) (PreH17 : (width = total)) (PreH18 : ((Zlength (vals_l_2)) = total)) (PreH19 : ((Zlength (dp_l_2)) = (total * width))) (PreH20 : (1 <= (n_pre + 1))) (PreH21 : (EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1))) (PreH22 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH23 : ((Zlength (dp_l_2)) = (total * width))) (PreH24 : (width = total)) (PreH25 : ((0 : Int) <= start)) (PreH26 : (start <= n_pre)) (PreH27 : ((0 : Int) <= answer)) (PreH28 : (answer <= 2100000000)) (PreH29 : (EnergyAnswerBest vals_l_2 n_pre start answer)) (PreH30 : (EnergyIntervalBest vals_l_2 start ((start + n_pre) - 1) value)) (PreH31 : ((Zlength (beads_l)) = n_pre)) (PreH32 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH33 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH34 : forall (ev_2 : (List Int)) , forall (start_3 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_3)) ∧ (start_3 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  forall (ev : (List Int)) , forall (start_2 : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start_2)) ∧ (start_2 < n_pre)) ∧ (EnergyIntervalPlan ev start_2 ((start_2 + n_pre) - 1) energy)) -> (energy <= 2100000000))

noncomputable def energyNecklace_entail_wit_20_2_split_goal_2 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (start : Int) (value : Int) (answer : Int) (PreH1 : (value <= answer)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((0 : Int) <= start)) (PreH9 : (start < n_pre)) (PreH10 : (value = (Znth ((((start * width) + start) + n_pre) - 1) dp_l_2 (0 : Int)))) (PreH11 : ((0 : Int) <= value)) (PreH12 : (value <= 2100000000)) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : ((Zlength (dp_l_2)) = (total * width))) (PreH15 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH16 : ((0 : Int) <= total)) (PreH17 : (width = total)) (PreH18 : ((Zlength (vals_l_2)) = total)) (PreH19 : ((Zlength (dp_l_2)) = (total * width))) (PreH20 : (1 <= (n_pre + 1))) (PreH21 : (EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1))) (PreH22 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH23 : ((Zlength (dp_l_2)) = (total * width))) (PreH24 : (width = total)) (PreH25 : ((0 : Int) <= start)) (PreH26 : (start <= n_pre)) (PreH27 : ((0 : Int) <= answer)) (PreH28 : (answer <= 2100000000)) (PreH29 : (EnergyAnswerBest vals_l_2 n_pre start answer)) (PreH30 : (EnergyIntervalBest vals_l_2 start ((start + n_pre) - 1) value)) (PreH31 : ((Zlength (beads_l)) = n_pre)) (PreH32 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH33 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH34 : forall (ev_2 : (List Int)) , forall (start_3 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_3)) ∧ (start_3 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (EnergyAnswerBest vals_l_2 n_pre (start + 1) answer)

noncomputable def energyNecklace_entail_wit_21 : Prop :=
  (
forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (start_2 : Int) (value : Int) (answer : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((0 : Int) <= start_2)) (PreH8 : (start_2 < n_pre)) (PreH9 : (value = (Znth ((((start_2 * width) + start_2) + n_pre) - 1) dp_l_2 (0 : Int)))) (PreH10 : ((0 : Int) <= value)) (PreH11 : (value <= 2100000000)) (PreH12 : ((0 : Int) <= answer)) (PreH13 : (answer <= 2100000000)) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : ((Zlength (dp_l_2)) = (total * width))) (PreH16 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH17 : ((0 : Int) <= total)) (PreH18 : (width = total)) (PreH19 : ((Zlength (vals_l_2)) = total)) (PreH20 : ((Zlength (dp_l_2)) = (total * width))) (PreH21 : (1 <= (n_pre + 1))) (PreH22 : (EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1))) (PreH23 : (EnergyIntervalBest vals_l_2 start_2 ((start_2 + n_pre) - 1) value)) (PreH24 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH25 : ((Zlength (dp_l_2)) = (total * width))) (PreH26 : (width = total)) (PreH27 : ((0 : Int) <= (start_2 + 1))) (PreH28 : ((start_2 + 1) <= n_pre)) (PreH29 : ((0 : Int) <= answer)) (PreH30 : (answer <= 2100000000)) (PreH31 : (EnergyAnswerBest vals_l_2 n_pre (start_2 + 1) answer)) (PreH32 : ((Zlength (beads_l)) = n_pre)) (PreH33 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH34 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH35 : forall (ev_2 : (List Int)) , forall (start_3 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_3)) ∧ (start_3 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l_2)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l_2)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  EX vals_l : (List Int), EX dp_l : (List Int),
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((0 : Int) <= (start_2 + 1)) ” &&
  “ ((start_2 + 1) <= n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 2100000000) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (width = total) ” &&
  “ ((Zlength (vals_l)) = total) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (1 <= (n_pre + 1)) ” &&
  “ (EnergyLengthsComplete vals_l dp_l width (n_pre + 1)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (width = total) ” &&
  “ ((0 : Int) <= (start_2 + 1)) ” &&
  “ ((start_2 + 1) <= n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 2100000000) ” &&
  “ (EnergyAnswerBest vals_l n_pre (start_2 + 1) answer) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) beads_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) beads_l) ” &&
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
) \/
(
forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (start_2 : Int) (value : Int) (answer : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((0 : Int) <= start_2)) (PreH8 : (start_2 < n_pre)) (PreH9 : (value = (Znth ((((start_2 * width) + start_2) + n_pre) - 1) dp_l_2 (0 : Int)))) (PreH10 : ((0 : Int) <= value)) (PreH11 : (value <= 2100000000)) (PreH12 : ((0 : Int) <= answer)) (PreH13 : (answer <= 2100000000)) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : ((Zlength (dp_l_2)) = (total * width))) (PreH16 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH17 : ((0 : Int) <= total)) (PreH18 : (width = total)) (PreH19 : ((Zlength (vals_l_2)) = total)) (PreH20 : ((Zlength (dp_l_2)) = (total * width))) (PreH21 : (1 <= (n_pre + 1))) (PreH22 : (EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1))) (PreH23 : (EnergyIntervalBest vals_l_2 start_2 ((start_2 + n_pre) - 1) value)) (PreH24 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH25 : ((Zlength (dp_l_2)) = (total * width))) (PreH26 : (width = total)) (PreH27 : ((0 : Int) <= (start_2 + 1))) (PreH28 : ((start_2 + 1) <= n_pre)) (PreH29 : ((0 : Int) <= answer)) (PreH30 : (answer <= 2100000000)) (PreH31 : (EnergyAnswerBest vals_l_2 n_pre (start_2 + 1) answer)) (PreH32 : ((Zlength (beads_l)) = n_pre)) (PreH33 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH34 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH35 : forall (ev_2 : (List Int)) , forall (start_3 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_3)) ∧ (start_3 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  TT && emp 
|--
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  emp
)

noncomputable def energyNecklace_entail_wit_21_split_goal_1 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l_2 : (List Int)) (dp_l_2 : (List Int)) (total : Int) (width : Int) (start_2 : Int) (value : Int) (answer : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((0 : Int) <= start_2)) (PreH8 : (start_2 < n_pre)) (PreH9 : (value = (Znth ((((start_2 * width) + start_2) + n_pre) - 1) dp_l_2 (0 : Int)))) (PreH10 : ((0 : Int) <= value)) (PreH11 : (value <= 2100000000)) (PreH12 : ((0 : Int) <= answer)) (PreH13 : (answer <= 2100000000)) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : ((Zlength (dp_l_2)) = (total * width))) (PreH16 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH17 : ((0 : Int) <= total)) (PreH18 : (width = total)) (PreH19 : ((Zlength (vals_l_2)) = total)) (PreH20 : ((Zlength (dp_l_2)) = (total * width))) (PreH21 : (1 <= (n_pre + 1))) (PreH22 : (EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1))) (PreH23 : (EnergyIntervalBest vals_l_2 start_2 ((start_2 + n_pre) - 1) value)) (PreH24 : (EnergyValsDuplicated beads_l vals_l_2 n_pre)) (PreH25 : ((Zlength (dp_l_2)) = (total * width))) (PreH26 : (width = total)) (PreH27 : ((0 : Int) <= (start_2 + 1))) (PreH28 : ((start_2 + 1) <= n_pre)) (PreH29 : ((0 : Int) <= answer)) (PreH30 : (answer <= 2100000000)) (PreH31 : (EnergyAnswerBest vals_l_2 n_pre (start_2 + 1) answer)) (PreH32 : ((Zlength (beads_l)) = n_pre)) (PreH33 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH34 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH35 : forall (ev_2 : (List Int)) , forall (start_3 : Int) , forall (energy_2 : Int) , (((((EnergyValsDuplicated beads_l ev_2 n_pre) ∧ ((0 : Int) <= start_3)) ∧ (start_3 < n_pre)) ∧ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre) - 1) energy_2)) -> (energy_2 <= 2100000000))) ,
  forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))

noncomputable def energyNecklace_entail_wit_22 : Prop :=
  (
forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (answer : Int) (start_2 : Int) (width : Int) (total : Int) (PreH1 : (start_2 >= n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((0 : Int) <= start_2)) (PreH9 : (start_2 <= n_pre)) (PreH10 : ((0 : Int) <= answer)) (PreH11 : (answer <= 2100000000)) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l)) = total)) (PreH18 : ((Zlength (dp_l)) = (total * width))) (PreH19 : (1 <= (n_pre + 1))) (PreH20 : (EnergyLengthsComplete vals_l dp_l width (n_pre + 1))) (PreH21 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH22 : ((Zlength (dp_l)) = (total * width))) (PreH23 : (width = total)) (PreH24 : ((0 : Int) <= start_2)) (PreH25 : (start_2 <= n_pre)) (PreH26 : ((0 : Int) <= answer)) (PreH27 : (answer <= 2100000000)) (PreH28 : (EnergyAnswerBest vals_l n_pre start_2 answer)) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH31 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH32 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "width" ) )) # Int |-> (width))
  ** ((( &( "answer" ) )) # Int |-> (answer))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ (EnergyNecklaceAnswer beads_l n_pre answer) ”
  &&  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.undef_full ( &( "vals" ) ) 200)
  ** (intArray.undef_full ( &( "dp" ) ) 40000)
  ** ((( &( "total" ) )) # Int |->_)
  ** ((( &( "width" ) )) # Int |->_)
  ** ((( &( "answer" ) )) # Int |->_)
) \/
(
forall (beads_l : (List Int)) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (answer : Int) (start_2 : Int) (width : Int) (total : Int) (PreH1 : (start_2 >= n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((0 : Int) <= start_2)) (PreH9 : (start_2 <= n_pre)) (PreH10 : ((0 : Int) <= answer)) (PreH11 : (answer <= 2100000000)) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l)) = total)) (PreH18 : ((Zlength (dp_l)) = (total * width))) (PreH19 : (1 <= (n_pre + 1))) (PreH20 : (EnergyLengthsComplete vals_l dp_l width (n_pre + 1))) (PreH21 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH22 : ((Zlength (dp_l)) = (total * width))) (PreH23 : (width = total)) (PreH24 : ((0 : Int) <= start_2)) (PreH25 : (start_2 <= n_pre)) (PreH26 : ((0 : Int) <= answer)) (PreH27 : (answer <= 2100000000)) (PreH28 : (EnergyAnswerBest vals_l n_pre start_2 answer)) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH31 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH32 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ (EnergyNecklaceAnswer beads_l n_pre answer) ”
  &&  (intArray.undef_full ( &( "vals" ) ) 200)
  ** (intArray.undef_full ( &( "dp" ) ) 40000)
)

noncomputable def energyNecklace_entail_wit_22_split_goal_1 : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (answer : Int) (start_2 : Int) (width : Int) (total : Int) (PreH1 : (start_2 >= n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((0 : Int) <= start_2)) (PreH9 : (start_2 <= n_pre)) (PreH10 : ((0 : Int) <= answer)) (PreH11 : (answer <= 2100000000)) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l)) = total)) (PreH18 : ((Zlength (dp_l)) = (total * width))) (PreH19 : (1 <= (n_pre + 1))) (PreH20 : (EnergyLengthsComplete vals_l dp_l width (n_pre + 1))) (PreH21 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH22 : ((Zlength (dp_l)) = (total * width))) (PreH23 : (width = total)) (PreH24 : ((0 : Int) <= start_2)) (PreH25 : (start_2 <= n_pre)) (PreH26 : ((0 : Int) <= answer)) (PreH27 : (answer <= 2100000000)) (PreH28 : (EnergyAnswerBest vals_l n_pre start_2 answer)) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH31 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH32 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ (EnergyNecklaceAnswer beads_l n_pre answer) ”

noncomputable def energyNecklace_entail_wit_22_split_goal_spatial : Prop :=
  forall (beads_l : (List Int)) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (answer : Int) (start_2 : Int) (width : Int) (total : Int) (PreH1 : (start_2 >= n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((0 : Int) <= start_2)) (PreH9 : (start_2 <= n_pre)) (PreH10 : ((0 : Int) <= answer)) (PreH11 : (answer <= 2100000000)) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l)) = (total * width))) (PreH14 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l)) = total)) (PreH18 : ((Zlength (dp_l)) = (total * width))) (PreH19 : (1 <= (n_pre + 1))) (PreH20 : (EnergyLengthsComplete vals_l dp_l width (n_pre + 1))) (PreH21 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH22 : ((Zlength (dp_l)) = (total * width))) (PreH23 : (width = total)) (PreH24 : ((0 : Int) <= start_2)) (PreH25 : (start_2 <= n_pre)) (PreH26 : ((0 : Int) <= answer)) (PreH27 : (answer <= 2100000000)) (PreH28 : (EnergyAnswerBest vals_l n_pre start_2 answer)) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH31 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH32 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  (intArray.undef_full ( &( "vals" ) ) 200)
  ** (intArray.undef_full ( &( "dp" ) ) 40000)

noncomputable def energyNecklace_return_wit_1 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (result : Int) (PreH1 : (EnergyNecklaceAnswer beads_l n_pre result)) ,
  (intArray.full beads_pre n_pre beads_l)
|--
  “ (EnergyNecklaceAnswer beads_l n_pre result) ”
  &&  (intArray.full beads_pre n_pre beads_l)

noncomputable def energyNecklace_partial_solve_wit_1 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (i : Int) (vals_l : (List Int)) (width : Int) (total : Int) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 Eq (sublist ((0 : Int)) (i) (vals_l)) (sublist ((0 : Int)) (i) (beads_l)))) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH15 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH16 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.seg ( &( "vals" ) ) (0 : Int) i vals_l)
  ** (intArray.undef_seg ( &( "vals" ) ) i total)
  ** (intArray.undef_full ( &( "dp" ) ) (total * width))
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ (i < n_pre) ” &&
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (vals_l)) = i) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (Forall2 Eq (sublist ((0 : Int)) (i) (vals_l)) (sublist ((0 : Int)) (i) (beads_l))) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) beads_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) beads_l) ” &&
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  (((beads_pre + (i * sizeof(INT)))) # Int |-> ((Znth i beads_l (0 : Int))))
  ** (intArray.missing_i beads_pre i (0 : Int) n_pre beads_l)
  ** (intArray.seg ( &( "vals" ) ) (0 : Int) i vals_l)
  ** (intArray.undef_seg ( &( "vals" ) ) i total)
  ** (intArray.undef_full ( &( "dp" ) ) (total * width))
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)

noncomputable def energyNecklace_partial_solve_wit_2 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (i : Int) (vals_l : (List Int)) (width : Int) (total : Int) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 Eq (sublist ((0 : Int)) (i) (vals_l)) (sublist ((0 : Int)) (i) (beads_l)))) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH15 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH16 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.seg ( &( "vals" ) ) (0 : Int) i vals_l)
  ** (intArray.undef_seg ( &( "vals" ) ) i total)
  ** (intArray.undef_full ( &( "dp" ) ) (total * width))
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ (i < n_pre) ” &&
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (vals_l)) = i) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (Forall2 Eq (sublist ((0 : Int)) (i) (vals_l)) (sublist ((0 : Int)) (i) (beads_l))) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) beads_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) beads_l) ” &&
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  (((( &( "vals" ) ) + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg ( &( "vals" ) ) (i + 1) total)
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.seg ( &( "vals" ) ) (0 : Int) i vals_l)
  ** (intArray.undef_full ( &( "dp" ) ) (total * width))
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)

noncomputable def energyNecklace_partial_solve_wit_3 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (i : Int) (vals_l : (List Int)) (width : Int) (total : Int) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l)) = (n_pre + i))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 Eq (sublist ((0 : Int)) (n_pre) (vals_l)) (sublist ((0 : Int)) (n_pre) (beads_l)))) (PreH13 : (Forall2 Eq (sublist (n_pre) ((n_pre + i)) (vals_l)) (sublist ((0 : Int)) (i) (beads_l)))) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH16 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH17 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.seg ( &( "vals" ) ) (0 : Int) (n_pre + i) vals_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (n_pre + i) total)
  ** (intArray.undef_full ( &( "dp" ) ) (total * width))
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ (i < n_pre) ” &&
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (vals_l)) = (n_pre + i)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (Forall2 Eq (sublist ((0 : Int)) (n_pre) (vals_l)) (sublist ((0 : Int)) (n_pre) (beads_l))) ” &&
  “ (Forall2 Eq (sublist (n_pre) ((n_pre + i)) (vals_l)) (sublist ((0 : Int)) (i) (beads_l))) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) beads_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) beads_l) ” &&
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  (((beads_pre + (i * sizeof(INT)))) # Int |-> ((Znth i beads_l (0 : Int))))
  ** (intArray.missing_i beads_pre i (0 : Int) n_pre beads_l)
  ** (intArray.seg ( &( "vals" ) ) (0 : Int) (n_pre + i) vals_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (n_pre + i) total)
  ** (intArray.undef_full ( &( "dp" ) ) (total * width))
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)

noncomputable def energyNecklace_partial_solve_wit_4 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (i : Int) (vals_l : (List Int)) (width : Int) (total : Int) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l)) = (n_pre + i))) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 Eq (sublist ((0 : Int)) (n_pre) (vals_l)) (sublist ((0 : Int)) (n_pre) (beads_l)))) (PreH13 : (Forall2 Eq (sublist (n_pre) ((n_pre + i)) (vals_l)) (sublist ((0 : Int)) (i) (beads_l)))) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH16 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH17 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.seg ( &( "vals" ) ) (0 : Int) (n_pre + i) vals_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (n_pre + i) total)
  ** (intArray.undef_full ( &( "dp" ) ) (total * width))
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ (i < n_pre) ” &&
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (vals_l)) = (n_pre + i)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (Forall2 Eq (sublist ((0 : Int)) (n_pre) (vals_l)) (sublist ((0 : Int)) (n_pre) (beads_l))) ” &&
  “ (Forall2 Eq (sublist (n_pre) ((n_pre + i)) (vals_l)) (sublist ((0 : Int)) (i) (beads_l))) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) beads_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) beads_l) ” &&
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  (((( &( "vals" ) ) + ((n_pre + i) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg ( &( "vals" ) ) ((n_pre + i) + 1) total)
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.seg ( &( "vals" ) ) (0 : Int) (n_pre + i) vals_l)
  ** (intArray.undef_full ( &( "dp" ) ) (total * width))
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)

noncomputable def energyNecklace_partial_solve_wit_5 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (i : Int) (dp_l : (List Int)) (width : Int) (total : Int) (PreH1 : (i < (total * width))) (PreH2 : (total = (2 * n_pre))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = i)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i <= (total * width))) (PreH12 : (Forall (Eq ((0 : Int))) dp_l)) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH16 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH17 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) i dp_l)
  ** (intArray.undef_seg ( &( "dp" ) ) i (total * width))
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ (i < (total * width)) ” &&
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = i) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (total * width)) ” &&
  “ (Forall (Eq ((0 : Int))) dp_l) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) beads_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) beads_l) ” &&
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  (((( &( "dp" ) ) + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg ( &( "dp" ) ) (i + 1) (total * width))
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.seg ( &( "dp" ) ) (0 : Int) i dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)

noncomputable def energyNecklace_partial_solve_wit_6 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : ((0 : Int) <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH36 : (2 <= len)) (PreH37 : ((0 : Int) <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH39 : ((left + len) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len) - 1))) (PreH42 : ((0 : Int) <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best)) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH48 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (total - len)) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left <= split) ” &&
  “ (split < right) ” &&
  “ ((0 : Int) <= right) ” &&
  “ (right < total) ” &&
  “ ((right + 1) < total) ” &&
  “ ((0 : Int) <= ((left * width) + split)) ” &&
  “ (((left * width) + split) < (total * width)) ” &&
  “ ((0 : Int) <= (((split + 1) * width) + right)) ” &&
  “ ((((split + 1) * width) + right) < (total * width)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < total) ” &&
  “ ((0 : Int) <= (split + 1)) ” &&
  “ ((split + 1) < total) ” &&
  “ ((0 : Int) <= (right + 1)) ” &&
  “ ((right + 1) < total) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (width = total) ” &&
  “ ((Zlength (vals_l)) = total) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (1 <= len) ” &&
  “ (EnergyLengthsComplete vals_l dp_l width len) ” &&
  “ (2 <= len) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (EnergyLeftComplete vals_l dp_l width len left) ” &&
  “ ((left + len) <= total) ” &&
  “ (left <= split) ” &&
  “ (split <= ((left + len) - 1)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 2100000000) ” &&
  “ (EnergySplitBest vals_l dp_l width len left split best) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) beads_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) beads_l) ” &&
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  (((( &( "dp" ) ) + (((left * width) + split) * sizeof(INT)))) # Int |-> ((Znth ((left * width) + split) dp_l (0 : Int))))
  ** (intArray.missing_i ( &( "dp" ) ) ((left * width) + split) (0 : Int) (total * width) dp_l)
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)

noncomputable def energyNecklace_partial_solve_wit_7 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : ((0 : Int) <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH36 : (2 <= len)) (PreH37 : ((0 : Int) <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH39 : ((left + len) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len) - 1))) (PreH42 : ((0 : Int) <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best)) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH48 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (total - len)) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left <= split) ” &&
  “ (split < right) ” &&
  “ ((0 : Int) <= right) ” &&
  “ (right < total) ” &&
  “ ((right + 1) < total) ” &&
  “ ((0 : Int) <= ((left * width) + split)) ” &&
  “ (((left * width) + split) < (total * width)) ” &&
  “ ((0 : Int) <= (((split + 1) * width) + right)) ” &&
  “ ((((split + 1) * width) + right) < (total * width)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < total) ” &&
  “ ((0 : Int) <= (split + 1)) ” &&
  “ ((split + 1) < total) ” &&
  “ ((0 : Int) <= (right + 1)) ” &&
  “ ((right + 1) < total) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (width = total) ” &&
  “ ((Zlength (vals_l)) = total) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (1 <= len) ” &&
  “ (EnergyLengthsComplete vals_l dp_l width len) ” &&
  “ (2 <= len) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (EnergyLeftComplete vals_l dp_l width len left) ” &&
  “ ((left + len) <= total) ” &&
  “ (left <= split) ” &&
  “ (split <= ((left + len) - 1)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 2100000000) ” &&
  “ (EnergySplitBest vals_l dp_l width len left split best) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) beads_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) beads_l) ” &&
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  (((( &( "dp" ) ) + ((((split + 1) * width) + right) * sizeof(INT)))) # Int |-> ((Znth (((split + 1) * width) + right) dp_l (0 : Int))))
  ** (intArray.missing_i ( &( "dp" ) ) (((split + 1) * width) + right) (0 : Int) (total * width) dp_l)
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)

noncomputable def energyNecklace_partial_solve_wit_8 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : ((0 : Int) <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH36 : (2 <= len)) (PreH37 : ((0 : Int) <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH39 : ((left + len) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len) - 1))) (PreH42 : ((0 : Int) <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best)) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH48 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (total - len)) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left <= split) ” &&
  “ (split < right) ” &&
  “ ((0 : Int) <= right) ” &&
  “ (right < total) ” &&
  “ ((right + 1) < total) ” &&
  “ ((0 : Int) <= ((left * width) + split)) ” &&
  “ (((left * width) + split) < (total * width)) ” &&
  “ ((0 : Int) <= (((split + 1) * width) + right)) ” &&
  “ ((((split + 1) * width) + right) < (total * width)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < total) ” &&
  “ ((0 : Int) <= (split + 1)) ” &&
  “ ((split + 1) < total) ” &&
  “ ((0 : Int) <= (right + 1)) ” &&
  “ ((right + 1) < total) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (width = total) ” &&
  “ ((Zlength (vals_l)) = total) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (1 <= len) ” &&
  “ (EnergyLengthsComplete vals_l dp_l width len) ” &&
  “ (2 <= len) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (EnergyLeftComplete vals_l dp_l width len left) ” &&
  “ ((left + len) <= total) ” &&
  “ (left <= split) ” &&
  “ (split <= ((left + len) - 1)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 2100000000) ” &&
  “ (EnergySplitBest vals_l dp_l width len left split best) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) beads_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) beads_l) ” &&
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  (((( &( "vals" ) ) + (left * sizeof(INT)))) # Int |-> ((Znth left vals_l (0 : Int))))
  ** (intArray.missing_i ( &( "vals" ) ) left (0 : Int) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)

noncomputable def energyNecklace_partial_solve_wit_9 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : ((0 : Int) <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH36 : (2 <= len)) (PreH37 : ((0 : Int) <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH39 : ((left + len) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len) - 1))) (PreH42 : ((0 : Int) <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best)) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH48 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (total - len)) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left <= split) ” &&
  “ (split < right) ” &&
  “ ((0 : Int) <= right) ” &&
  “ (right < total) ” &&
  “ ((right + 1) < total) ” &&
  “ ((0 : Int) <= ((left * width) + split)) ” &&
  “ (((left * width) + split) < (total * width)) ” &&
  “ ((0 : Int) <= (((split + 1) * width) + right)) ” &&
  “ ((((split + 1) * width) + right) < (total * width)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < total) ” &&
  “ ((0 : Int) <= (split + 1)) ” &&
  “ ((split + 1) < total) ” &&
  “ ((0 : Int) <= (right + 1)) ” &&
  “ ((right + 1) < total) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (width = total) ” &&
  “ ((Zlength (vals_l)) = total) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (1 <= len) ” &&
  “ (EnergyLengthsComplete vals_l dp_l width len) ” &&
  “ (2 <= len) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (EnergyLeftComplete vals_l dp_l width len left) ” &&
  “ ((left + len) <= total) ” &&
  “ (left <= split) ” &&
  “ (split <= ((left + len) - 1)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 2100000000) ” &&
  “ (EnergySplitBest vals_l dp_l width len left split best) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) beads_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) beads_l) ” &&
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  (((( &( "vals" ) ) + ((split + 1) * sizeof(INT)))) # Int |-> ((Znth (split + 1) vals_l (0 : Int))))
  ** (intArray.missing_i ( &( "vals" ) ) (split + 1) (0 : Int) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)

noncomputable def energyNecklace_partial_solve_wit_10 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((0 : Int) <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1) < total)) (PreH17 : ((0 : Int) <= ((left * width) + split))) (PreH18 : (((left * width) + split) < (total * width))) (PreH19 : ((0 : Int) <= (((split + 1) * width) + right))) (PreH20 : ((((split + 1) * width) + right) < (total * width))) (PreH21 : ((0 : Int) <= left)) (PreH22 : (left < total)) (PreH23 : ((0 : Int) <= (split + 1))) (PreH24 : ((split + 1) < total)) (PreH25 : ((0 : Int) <= (right + 1))) (PreH26 : ((right + 1) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH30 : ((0 : Int) <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH36 : (2 <= len)) (PreH37 : ((0 : Int) <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH39 : ((left + len) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len) - 1))) (PreH42 : ((0 : Int) <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best)) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH47 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH48 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (total - len)) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ (left <= split) ” &&
  “ (split < right) ” &&
  “ ((0 : Int) <= right) ” &&
  “ (right < total) ” &&
  “ ((right + 1) < total) ” &&
  “ ((0 : Int) <= ((left * width) + split)) ” &&
  “ (((left * width) + split) < (total * width)) ” &&
  “ ((0 : Int) <= (((split + 1) * width) + right)) ” &&
  “ ((((split + 1) * width) + right) < (total * width)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < total) ” &&
  “ ((0 : Int) <= (split + 1)) ” &&
  “ ((split + 1) < total) ” &&
  “ ((0 : Int) <= (right + 1)) ” &&
  “ ((right + 1) < total) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (width = total) ” &&
  “ ((Zlength (vals_l)) = total) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (1 <= len) ” &&
  “ (EnergyLengthsComplete vals_l dp_l width len) ” &&
  “ (2 <= len) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (EnergyLeftComplete vals_l dp_l width len left) ” &&
  “ ((left + len) <= total) ” &&
  “ (left <= split) ” &&
  “ (split <= ((left + len) - 1)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 2100000000) ” &&
  “ (EnergySplitBest vals_l dp_l width len left split best) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) beads_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) beads_l) ” &&
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  (((( &( "vals" ) ) + ((right + 1) * sizeof(INT)))) # Int |-> ((Znth (right + 1) vals_l (0 : Int))))
  ** (intArray.missing_i ( &( "vals" ) ) (right + 1) (0 : Int) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)

noncomputable def energyNecklace_partial_solve_wit_11 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (len : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((0 : Int) <= left)) (PreH10 : (left < (total - len))) (PreH11 : (right = ((left + len) - 1))) (PreH12 : ((right + 1) < total)) (PreH13 : ((0 : Int) <= ((left * width) + right))) (PreH14 : (((left * width) + right) < (total * width))) (PreH15 : ((0 : Int) <= best)) (PreH16 : (best <= 2100000000)) (PreH17 : ((Zlength (beads_l)) = n_pre)) (PreH18 : ((Zlength (dp_l)) = (total * width))) (PreH19 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (width = total)) (PreH22 : ((Zlength (vals_l)) = total)) (PreH23 : ((Zlength (dp_l)) = (total * width))) (PreH24 : (1 <= len)) (PreH25 : (EnergyLengthsComplete vals_l dp_l width len)) (PreH26 : (2 <= len)) (PreH27 : ((0 : Int) <= left)) (PreH28 : (EnergyLeftComplete vals_l dp_l width len left)) (PreH29 : ((left + len) <= total)) (PreH30 : (left <= right)) (PreH31 : (right <= ((left + len) - 1))) (PreH32 : ((0 : Int) <= best)) (PreH33 : (best <= 2100000000)) (PreH34 : (EnergySplitBest vals_l dp_l width len left right best)) (PreH35 : (EnergyIntervalBest vals_l left right best)) (PreH36 : ((Zlength (beads_l)) = n_pre)) (PreH37 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH39 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ (2 <= len) ” &&
  “ (len <= n_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (total - len)) ” &&
  “ (right = ((left + len) - 1)) ” &&
  “ ((right + 1) < total) ” &&
  “ ((0 : Int) <= ((left * width) + right)) ” &&
  “ (((left * width) + right) < (total * width)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 2100000000) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (width = total) ” &&
  “ ((Zlength (vals_l)) = total) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (1 <= len) ” &&
  “ (EnergyLengthsComplete vals_l dp_l width len) ” &&
  “ (2 <= len) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (EnergyLeftComplete vals_l dp_l width len left) ” &&
  “ ((left + len) <= total) ” &&
  “ (left <= right) ” &&
  “ (right <= ((left + len) - 1)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 2100000000) ” &&
  “ (EnergySplitBest vals_l dp_l width len left right best) ” &&
  “ (EnergyIntervalBest vals_l left right best) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) beads_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) beads_l) ” &&
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  (((( &( "dp" ) ) + (((left * width) + right) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i ( &( "dp" ) ) ((left * width) + right) (0 : Int) (total * width) dp_l)
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)

noncomputable def energyNecklace_partial_solve_wit_12 : Prop :=
  forall (beads_l : (List Int)) (beads_pre : Int) (n_pre : Int) (vals_l : (List Int)) (dp_l : (List Int)) (total : Int) (width : Int) (start_2 : Int) (answer : Int) (PreH1 : (total = (2 * n_pre))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((0 : Int) <= start_2)) (PreH8 : (start_2 < n_pre)) (PreH9 : ((0 : Int) <= ((((start_2 * width) + start_2) + n_pre) - 1))) (PreH10 : (((((start_2 * width) + start_2) + n_pre) - 1) < (total * width))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width))) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH14 : ((0 : Int) <= total)) (PreH15 : (width = total)) (PreH16 : ((Zlength (vals_l)) = total)) (PreH17 : ((Zlength (dp_l)) = (total * width))) (PreH18 : (1 <= (n_pre + 1))) (PreH19 : (EnergyLengthsComplete vals_l dp_l width (n_pre + 1))) (PreH20 : (EnergyValsDuplicated beads_l vals_l n_pre)) (PreH21 : ((Zlength (dp_l)) = (total * width))) (PreH22 : (width = total)) (PreH23 : ((0 : Int) <= start_2)) (PreH24 : (start_2 <= n_pre)) (PreH25 : ((0 : Int) <= answer)) (PreH26 : (answer <= 2100000000)) (PreH27 : (EnergyAnswerBest vals_l n_pre start_2 answer)) (PreH28 : (EnergyIntervalBest vals_l start_2 ((start_2 + n_pre) - 1) (Znth ((((start_2 * width) + start_2) + n_pre) - 1) dp_l (0 : Int)))) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall ((LE.le (α := Int)) (1)) beads_l)) (PreH31 : (Forall ((GE.ge (α := Int)) (1000)) beads_l)) (PreH32 : forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000))) ,
  (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.full ( &( "dp" ) ) (total * width) dp_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)
|--
  “ (total = (2 * n_pre)) ” &&
  “ (width = total) ” &&
  “ (4 <= n_pre) ” &&
  “ (n_pre <= 100) ” &&
  “ (8 <= total) ” &&
  “ (total <= 200) ” &&
  “ ((0 : Int) <= start_2) ” &&
  “ (start_2 < n_pre) ” &&
  “ ((0 : Int) <= ((((start_2 * width) + start_2) + n_pre) - 1)) ” &&
  “ (((((start_2 * width) + start_2) + n_pre) - 1) < (total * width)) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (width = total) ” &&
  “ ((Zlength (vals_l)) = total) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (1 <= (n_pre + 1)) ” &&
  “ (EnergyLengthsComplete vals_l dp_l width (n_pre + 1)) ” &&
  “ (EnergyValsDuplicated beads_l vals_l n_pre) ” &&
  “ ((Zlength (dp_l)) = (total * width)) ” &&
  “ (width = total) ” &&
  “ ((0 : Int) <= start_2) ” &&
  “ (start_2 <= n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 2100000000) ” &&
  “ (EnergyAnswerBest vals_l n_pre start_2 answer) ” &&
  “ (EnergyIntervalBest vals_l start_2 ((start_2 + n_pre) - 1) (Znth ((((start_2 * width) + start_2) + n_pre) - 1) dp_l (0 : Int))) ” &&
  “ ((Zlength (beads_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) beads_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) beads_l) ” &&
  “ forall (ev : (List Int)) , forall (start : Int) , forall (energy : Int) , (((((EnergyValsDuplicated beads_l ev n_pre) ∧ ((0 : Int) <= start)) ∧ (start < n_pre)) ∧ (EnergyIntervalPlan ev start ((start + n_pre) - 1) energy)) -> (energy <= 2100000000)) ”
  &&  (((( &( "dp" ) ) + (((((start_2 * width) + start_2) + n_pre) - 1) * sizeof(INT)))) # Int |-> ((Znth ((((start_2 * width) + start_2) + n_pre) - 1) dp_l (0 : Int))))
  ** (intArray.missing_i ( &( "dp" ) ) ((((start_2 * width) + start_2) + n_pre) - 1) (0 : Int) (total * width) dp_l)
  ** (intArray.full beads_pre n_pre beads_l)
  ** (intArray.full ( &( "vals" ) ) total vals_l)
  ** (intArray.undef_seg ( &( "vals" ) ) (2 * n_pre) 200)
  ** (intArray.undef_seg ( &( "dp" ) ) ((2 * n_pre) * (2 * n_pre)) 40000)


structure VC_Correct : Type where
  proof_of_energyNecklace_safety_wit_1 : energyNecklace_safety_wit_1
  proof_of_energyNecklace_safety_wit_2 : energyNecklace_safety_wit_2
  proof_of_energyNecklace_safety_wit_3 : energyNecklace_safety_wit_3
  proof_of_energyNecklace_safety_wit_4 : energyNecklace_safety_wit_4
  proof_of_energyNecklace_safety_wit_5 : energyNecklace_safety_wit_5
  proof_of_energyNecklace_safety_wit_6 : energyNecklace_safety_wit_6
  proof_of_energyNecklace_safety_wit_7 : energyNecklace_safety_wit_7
  proof_of_energyNecklace_safety_wit_8 : energyNecklace_safety_wit_8
  proof_of_energyNecklace_safety_wit_9 : energyNecklace_safety_wit_9
  proof_of_energyNecklace_safety_wit_10 : energyNecklace_safety_wit_10
  proof_of_energyNecklace_safety_wit_11 : energyNecklace_safety_wit_11
  proof_of_energyNecklace_safety_wit_12 : energyNecklace_safety_wit_12
  proof_of_energyNecklace_safety_wit_13 : energyNecklace_safety_wit_13
  proof_of_energyNecklace_safety_wit_14 : energyNecklace_safety_wit_14
  proof_of_energyNecklace_safety_wit_15 : energyNecklace_safety_wit_15
  proof_of_energyNecklace_safety_wit_16 : energyNecklace_safety_wit_16
  proof_of_energyNecklace_safety_wit_17 : energyNecklace_safety_wit_17
  proof_of_energyNecklace_safety_wit_18 : energyNecklace_safety_wit_18
  proof_of_energyNecklace_safety_wit_19 : energyNecklace_safety_wit_19
  proof_of_energyNecklace_safety_wit_20 : energyNecklace_safety_wit_20
  proof_of_energyNecklace_safety_wit_21 : energyNecklace_safety_wit_21
  proof_of_energyNecklace_safety_wit_22 : energyNecklace_safety_wit_22
  proof_of_energyNecklace_safety_wit_23 : energyNecklace_safety_wit_23
  proof_of_energyNecklace_safety_wit_24 : energyNecklace_safety_wit_24
  proof_of_energyNecklace_safety_wit_26 : energyNecklace_safety_wit_26
  proof_of_energyNecklace_safety_wit_28 : energyNecklace_safety_wit_28
  proof_of_energyNecklace_safety_wit_29 : energyNecklace_safety_wit_29
  proof_of_energyNecklace_safety_wit_30 : energyNecklace_safety_wit_30
  proof_of_energyNecklace_safety_wit_33 : energyNecklace_safety_wit_33
  proof_of_energyNecklace_safety_wit_34 : energyNecklace_safety_wit_34
  proof_of_energyNecklace_safety_wit_35 : energyNecklace_safety_wit_35
  proof_of_energyNecklace_safety_wit_36 : energyNecklace_safety_wit_36
  proof_of_energyNecklace_safety_wit_37 : energyNecklace_safety_wit_37
  proof_of_energyNecklace_safety_wit_38 : energyNecklace_safety_wit_38
  proof_of_energyNecklace_safety_wit_39 : energyNecklace_safety_wit_39
  proof_of_energyNecklace_safety_wit_40 : energyNecklace_safety_wit_40
  proof_of_energyNecklace_safety_wit_41 : energyNecklace_safety_wit_41
  proof_of_energyNecklace_safety_wit_42 : energyNecklace_safety_wit_42
  proof_of_energyNecklace_safety_wit_43 : energyNecklace_safety_wit_43
  proof_of_energyNecklace_safety_wit_44 : energyNecklace_safety_wit_44
  proof_of_energyNecklace_safety_wit_45 : energyNecklace_safety_wit_45
  proof_of_energyNecklace_return_wit_1 : energyNecklace_return_wit_1
  proof_of_energyNecklace_partial_solve_wit_1 : energyNecklace_partial_solve_wit_1
  proof_of_energyNecklace_partial_solve_wit_2 : energyNecklace_partial_solve_wit_2
  proof_of_energyNecklace_partial_solve_wit_3 : energyNecklace_partial_solve_wit_3
  proof_of_energyNecklace_partial_solve_wit_4 : energyNecklace_partial_solve_wit_4
  proof_of_energyNecklace_partial_solve_wit_5 : energyNecklace_partial_solve_wit_5
  proof_of_energyNecklace_partial_solve_wit_6 : energyNecklace_partial_solve_wit_6
  proof_of_energyNecklace_partial_solve_wit_7 : energyNecklace_partial_solve_wit_7
  proof_of_energyNecklace_partial_solve_wit_8 : energyNecklace_partial_solve_wit_8
  proof_of_energyNecklace_partial_solve_wit_9 : energyNecklace_partial_solve_wit_9
  proof_of_energyNecklace_partial_solve_wit_10 : energyNecklace_partial_solve_wit_10
  proof_of_energyNecklace_partial_solve_wit_11 : energyNecklace_partial_solve_wit_11
  proof_of_energyNecklace_partial_solve_wit_12 : energyNecklace_partial_solve_wit_12
  proof_of_energyNecklace_safety_wit_25 : energyNecklace_safety_wit_25
  proof_of_energyNecklace_safety_wit_27 : energyNecklace_safety_wit_27
  proof_of_energyNecklace_safety_wit_31 : energyNecklace_safety_wit_31
  proof_of_energyNecklace_safety_wit_32 : energyNecklace_safety_wit_32
  proof_of_energyNecklace_entail_wit_1 : energyNecklace_entail_wit_1
  proof_of_energyNecklace_entail_wit_2 : energyNecklace_entail_wit_2
  proof_of_energyNecklace_entail_wit_3 : energyNecklace_entail_wit_3
  proof_of_energyNecklace_entail_wit_4 : energyNecklace_entail_wit_4
  proof_of_energyNecklace_entail_wit_5 : energyNecklace_entail_wit_5
  proof_of_energyNecklace_entail_wit_6 : energyNecklace_entail_wit_6
  proof_of_energyNecklace_entail_wit_7 : energyNecklace_entail_wit_7
  proof_of_energyNecklace_entail_wit_8 : energyNecklace_entail_wit_8
  proof_of_energyNecklace_entail_wit_9 : energyNecklace_entail_wit_9
  proof_of_energyNecklace_entail_wit_10 : energyNecklace_entail_wit_10
  proof_of_energyNecklace_entail_wit_11 : energyNecklace_entail_wit_11
  proof_of_energyNecklace_entail_wit_12_1 : energyNecklace_entail_wit_12_1
  proof_of_energyNecklace_entail_wit_12_2 : energyNecklace_entail_wit_12_2
  proof_of_energyNecklace_entail_wit_13 : energyNecklace_entail_wit_13
  proof_of_energyNecklace_entail_wit_14 : energyNecklace_entail_wit_14
  proof_of_energyNecklace_entail_wit_15 : energyNecklace_entail_wit_15
  proof_of_energyNecklace_entail_wit_16 : energyNecklace_entail_wit_16
  proof_of_energyNecklace_entail_wit_17 : energyNecklace_entail_wit_17
  proof_of_energyNecklace_entail_wit_18 : energyNecklace_entail_wit_18
  proof_of_energyNecklace_entail_wit_19 : energyNecklace_entail_wit_19
  proof_of_energyNecklace_entail_wit_20_1 : energyNecklace_entail_wit_20_1
  proof_of_energyNecklace_entail_wit_20_2 : energyNecklace_entail_wit_20_2
  proof_of_energyNecklace_entail_wit_21 : energyNecklace_entail_wit_21
  proof_of_energyNecklace_entail_wit_22 : energyNecklace_entail_wit_22

end SimpleC.EE.LLM_bench.Algorithms.energy_necklace.energy_necklace_goal
