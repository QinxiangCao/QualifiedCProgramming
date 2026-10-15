import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P047_1523C_compression_and_expansion_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def solver_safety_wit_1 : Prop :=
  forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (PreH1 : (1 <= (Zlength (last_numbers)))) (PreH2 : ((Zlength (last_numbers)) <= 1000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (last_numbers)))) -> ((1 <= (Znth i last_numbers (0 : Int))) ∧ ((Znth i last_numbers (0 : Int)) <= (Zlength (last_numbers)))))) (PreH4 : (Pre last_numbers)) (PreH5 : (n_pre = (Zlength (last_numbers)))) ,
  ((( &( "total" ) )) # Int |->_)
  ** ((( &( "depth" ) )) # Int |-> ((0 : Int)))
  ** (intArray.undef_full ( &( "stack" ) ) 1005)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "flat" ) )) # Ptr |-> (flat_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** (intArray.full values_pre n_pre last_numbers)
  ** (intArray.undef_full flat_pre (n_pre * n_pre))
  ** (intArray.undef_full lengths_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (PreH1 : (1 <= (Zlength (last_numbers)))) (PreH2 : ((Zlength (last_numbers)) <= 1000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (last_numbers)))) -> ((1 <= (Znth i last_numbers (0 : Int))) ∧ ((Znth i last_numbers (0 : Int)) <= (Zlength (last_numbers)))))) (PreH4 : (Pre last_numbers)) (PreH5 : (n_pre = (Zlength (last_numbers)))) ,
  ((( &( "depth" ) )) # Int |->_)
  ** (intArray.undef_full ( &( "stack" ) ) 1005)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "flat" ) )) # Ptr |-> (flat_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** (intArray.full values_pre n_pre last_numbers)
  ** (intArray.undef_full flat_pre (n_pre * n_pre))
  ** (intArray.undef_full lengths_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (PreH1 : (1 <= (Zlength (last_numbers)))) (PreH2 : ((Zlength (last_numbers)) <= 1000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (last_numbers)))) -> ((1 <= (Znth i last_numbers (0 : Int))) ∧ ((Znth i last_numbers (0 : Int)) <= (Zlength (last_numbers)))))) (PreH4 : (Pre last_numbers)) (PreH5 : (n_pre = (Zlength (last_numbers)))) ,
  ((( &( "line" ) )) # Int |->_)
  ** ((( &( "total" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "depth" ) )) # Int |-> ((0 : Int)))
  ** (intArray.undef_full ( &( "stack" ) ) 1005)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "flat" ) )) # Ptr |-> (flat_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** (intArray.full values_pre n_pre last_numbers)
  ** (intArray.undef_full flat_pre (n_pre * n_pre))
  ** (intArray.undef_full lengths_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (cells : (List (Option Int))) (lengths_data : (List Int)) (flat_data : (List Int)) (total : Int) (active : (List Int)) (depth : Int) (line : Int) (items : (List (List Int))) (__default__App_option_Z : _App_option_Z) (PreH1 : (line < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (last_numbers)))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH6 : (Pre last_numbers)) (PreH7 : (Spec last_numbers items)) (PreH8 : ((Zlength (items)) = n_pre)) (PreH9 : ((0 : Int) <= line)) (PreH10 : (line <= n_pre)) (PreH11 : ((0 : Int) <= depth)) (PreH12 : (depth <= line)) (PreH13 : (depth = (Zlength (active)))) (PreH14 : (CurrentItem items line active)) (PreH15 : (BoundedItem n_pre active)) (PreH16 : (total = (Zlength (flat_data)))) (PreH17 : ((0 : Int) <= total)) (PreH18 : (total <= (line * n_pre))) (PreH19 : (FlatPrefix items line flat_data)) (PreH20 : (LengthsPrefix items line lengths_data)) (PreH21 : ((Zlength (cells)) = 1005)) (PreH22 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int))))))) ,
  (intArray.full values_pre n_pre last_numbers)
  ** ((( &( "x" ) )) # Int |-> ((Znth line last_numbers (0 : Int))))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "flat" ) )) # Ptr |-> (flat_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "line" ) )) # Int |-> (line))
  ** ((( &( "depth" ) )) # Int |-> (depth))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.mixed_full ( &( "stack" ) ) 1005 cells)
  ** (intArray.seg flat_pre (0 : Int) total flat_data)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) line lengths_data)
  ** (intArray.undef_seg lengths_pre line n_pre)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (cells : (List (Option Int))) (lengths_data : (List Int)) (flat_data : (List Int)) (total : Int) (active : (List Int)) (depth : Int) (line : Int) (items : (List (List Int))) (__default__App_option_Z : _App_option_Z) (PreH1 : ((Znth line last_numbers (0 : Int)) = 1)) (PreH2 : (line < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (n_pre = (Zlength (last_numbers)))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH7 : (Pre last_numbers)) (PreH8 : (Spec last_numbers items)) (PreH9 : ((Zlength (items)) = n_pre)) (PreH10 : ((0 : Int) <= line)) (PreH11 : (line <= n_pre)) (PreH12 : ((0 : Int) <= depth)) (PreH13 : (depth <= line)) (PreH14 : (depth = (Zlength (active)))) (PreH15 : (CurrentItem items line active)) (PreH16 : (BoundedItem n_pre active)) (PreH17 : (total = (Zlength (flat_data)))) (PreH18 : ((0 : Int) <= total)) (PreH19 : (total <= (line * n_pre))) (PreH20 : (FlatPrefix items line flat_data)) (PreH21 : (LengthsPrefix items line lengths_data)) (PreH22 : ((Zlength (cells)) = 1005)) (PreH23 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int))))))) ,
  (intArray.full values_pre n_pre last_numbers)
  ** ((( &( "x" ) )) # Int |-> ((Znth line last_numbers (0 : Int))))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "flat" ) )) # Ptr |-> (flat_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "line" ) )) # Int |-> (line))
  ** ((( &( "depth" ) )) # Int |-> (depth))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.mixed_full ( &( "stack" ) ) 1005 cells)
  ** (intArray.seg flat_pre (0 : Int) total flat_data)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) line lengths_data)
  ** (intArray.undef_seg lengths_pre line n_pre)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (cells : (List (Option Int))) (lengths_data : (List Int)) (flat_data : (List Int)) (total : Int) (active : (List Int)) (depth : Int) (line : Int) (items : (List (List Int))) (__default__App_option_Z : _App_option_Z) (PreH1 : ((Znth line last_numbers (0 : Int)) = 1)) (PreH2 : (line < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (n_pre = (Zlength (last_numbers)))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH7 : (Pre last_numbers)) (PreH8 : (Spec last_numbers items)) (PreH9 : ((Zlength (items)) = n_pre)) (PreH10 : ((0 : Int) <= line)) (PreH11 : (line <= n_pre)) (PreH12 : ((0 : Int) <= depth)) (PreH13 : (depth <= line)) (PreH14 : (depth = (Zlength (active)))) (PreH15 : (CurrentItem items line active)) (PreH16 : (BoundedItem n_pre active)) (PreH17 : (total = (Zlength (flat_data)))) (PreH18 : ((0 : Int) <= total)) (PreH19 : (total <= (line * n_pre))) (PreH20 : (FlatPrefix items line flat_data)) (PreH21 : (LengthsPrefix items line lengths_data)) (PreH22 : ((Zlength (cells)) = 1005)) (PreH23 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int))))))) ,
  (intArray.mixed_full ( &( "stack" ) ) 1005 (replace_Znth (depth) ((Some (1))) (cells)))
  ** (intArray.full values_pre n_pre last_numbers)
  ** ((( &( "x" ) )) # Int |-> ((Znth line last_numbers (0 : Int))))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "flat" ) )) # Ptr |-> (flat_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "line" ) )) # Int |-> (line))
  ** ((( &( "depth" ) )) # Int |-> (depth))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.seg flat_pre (0 : Int) total flat_data)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) line lengths_data)
  ** (intArray.undef_seg lengths_pre line n_pre)
|--
  “ ((depth + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (depth + 1)) ”

noncomputable def solver_safety_wit_7 : Prop :=
  (
forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (cells : (List (Option Int))) (lengths_data : (List Int)) (flat_data : (List Int)) (total : Int) (active : (List Int)) (depth : Int) (target : (List Int)) (x : Int) (line : Int) (items : (List (List Int))) (__default__App_option_Z : _App_option_Z) (PreH1 : (depth ≠ (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (last_numbers)))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH6 : (Pre last_numbers)) (PreH7 : (Spec last_numbers items)) (PreH8 : ((Zlength (items)) = n_pre)) (PreH9 : ((0 : Int) < line)) (PreH10 : (line < n_pre)) (PreH11 : (x = (Znth (line) (last_numbers) ((0 : Int))))) (PreH12 : (x ≠ 1)) (PreH13 : (target = (Znth (line) (items) ((@List.nil Int))))) (PreH14 : (1 <= depth)) (PreH15 : (depth <= line)) (PreH16 : (depth = (Zlength (active)))) (PreH17 : (PopTarget active target x)) (PreH18 : (BoundedItem n_pre active)) (PreH19 : (total = (Zlength (flat_data)))) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= (line * n_pre))) (PreH22 : (FlatPrefix items line flat_data)) (PreH23 : (LengthsPrefix items line lengths_data)) (PreH24 : ((Zlength (cells)) = 1005)) (PreH25 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int))))))) (PreH26 : ((Znth (depth - 1) cells __default__App_option_Z) = (Some ((Znth (depth - 1) active (0 : Int)))))) ,
  ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "flat" ) )) # Ptr |-> (flat_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "line" ) )) # Int |-> (line))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "depth" ) )) # Int |-> (depth))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full values_pre n_pre last_numbers)
  ** (((( &( "stack" ) ) + ((depth - 1) * sizeof(INT)))) # Int |-> ((Znth (depth - 1) active (0 : Int))))
  ** (intArray.mixed_missing_i ( &( "stack" ) ) (depth - 1) (0 : Int) 1005 cells)
  ** (intArray.seg flat_pre (0 : Int) total flat_data)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) line lengths_data)
  ** (intArray.undef_seg lengths_pre line n_pre)
|--
  “ (((Znth (depth - 1) active (0 : Int)) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth (depth - 1) active (0 : Int)) + 1)) ”
) \/
(
forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (cells : (List (Option Int))) (lengths_data : (List Int)) (flat_data : (List Int)) (total : Int) (active : (List Int)) (depth : Int) (target : (List Int)) (x : Int) (line : Int) (items : (List (List Int))) (__default__App_option_Z : _App_option_Z) (PreH1 : (depth ≠ (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (last_numbers)))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH6 : (Pre last_numbers)) (PreH7 : (Spec last_numbers items)) (PreH8 : ((Zlength (items)) = n_pre)) (PreH9 : ((0 : Int) < line)) (PreH10 : (line < n_pre)) (PreH11 : (x = (Znth (line) (last_numbers) ((0 : Int))))) (PreH12 : (x ≠ 1)) (PreH13 : (target = (Znth (line) (items) ((@List.nil Int))))) (PreH14 : (1 <= depth)) (PreH15 : (depth <= line)) (PreH16 : (depth = (Zlength (active)))) (PreH17 : (PopTarget active target x)) (PreH18 : (BoundedItem n_pre active)) (PreH19 : (total = (Zlength (flat_data)))) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= (line * n_pre))) (PreH22 : (FlatPrefix items line flat_data)) (PreH23 : (LengthsPrefix items line lengths_data)) (PreH24 : ((Zlength (cells)) = 1005)) (PreH25 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int))))))) (PreH26 : ((Znth (depth - 1) cells __default__App_option_Z) = (Some ((Znth (depth - 1) active (0 : Int)))))) ,
  ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "flat" ) )) # Ptr |-> (flat_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "line" ) )) # Int |-> (line))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "depth" ) )) # Int |-> (depth))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full values_pre n_pre last_numbers)
  ** (((( &( "stack" ) ) + ((depth - 1) * sizeof(INT)))) # Int |-> ((Znth (depth - 1) active (0 : Int))))
  ** (intArray.mixed_missing_i ( &( "stack" ) ) (depth - 1) (0 : Int) 1005 cells)
  ** (intArray.seg flat_pre (0 : Int) total flat_data)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) line lengths_data)
  ** (intArray.undef_seg lengths_pre line n_pre)
|--
  “ (((Znth (depth - 1) active (0 : Int)) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth (depth - 1) active (0 : Int)) + 1)) ”
)

noncomputable def solver_safety_wit_7_split_goal_1 : Prop :=
  forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (cells : (List (Option Int))) (lengths_data : (List Int)) (flat_data : (List Int)) (total : Int) (active : (List Int)) (depth : Int) (target : (List Int)) (x : Int) (line : Int) (items : (List (List Int))) (__default__App_option_Z : _App_option_Z) (PreH1 : (depth ≠ (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (last_numbers)))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH6 : (Pre last_numbers)) (PreH7 : (Spec last_numbers items)) (PreH8 : ((Zlength (items)) = n_pre)) (PreH9 : ((0 : Int) < line)) (PreH10 : (line < n_pre)) (PreH11 : (x = (Znth (line) (last_numbers) ((0 : Int))))) (PreH12 : (x ≠ 1)) (PreH13 : (target = (Znth (line) (items) ((@List.nil Int))))) (PreH14 : (1 <= depth)) (PreH15 : (depth <= line)) (PreH16 : (depth = (Zlength (active)))) (PreH17 : (PopTarget active target x)) (PreH18 : (BoundedItem n_pre active)) (PreH19 : (total = (Zlength (flat_data)))) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= (line * n_pre))) (PreH22 : (FlatPrefix items line flat_data)) (PreH23 : (LengthsPrefix items line lengths_data)) (PreH24 : ((Zlength (cells)) = 1005)) (PreH25 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int))))))) (PreH26 : ((Znth (depth - 1) cells __default__App_option_Z) = (Some ((Znth (depth - 1) active (0 : Int)))))) ,
  ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "flat" ) )) # Ptr |-> (flat_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "line" ) )) # Int |-> (line))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "depth" ) )) # Int |-> (depth))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full values_pre n_pre last_numbers)
  ** (((( &( "stack" ) ) + ((depth - 1) * sizeof(INT)))) # Int |-> ((Znth (depth - 1) active (0 : Int))))
  ** (intArray.mixed_missing_i ( &( "stack" ) ) (depth - 1) (0 : Int) 1005 cells)
  ** (intArray.seg flat_pre (0 : Int) total flat_data)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) line lengths_data)
  ** (intArray.undef_seg lengths_pre line n_pre)
|--
  “ (((Znth (depth - 1) active (0 : Int)) + 1) <= INT_MAX) ”

noncomputable def solver_safety_wit_7_split_goal_2 : Prop :=
  forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (cells : (List (Option Int))) (lengths_data : (List Int)) (flat_data : (List Int)) (total : Int) (active : (List Int)) (depth : Int) (target : (List Int)) (x : Int) (line : Int) (items : (List (List Int))) (__default__App_option_Z : _App_option_Z) (PreH1 : (depth ≠ (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (last_numbers)))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH6 : (Pre last_numbers)) (PreH7 : (Spec last_numbers items)) (PreH8 : ((Zlength (items)) = n_pre)) (PreH9 : ((0 : Int) < line)) (PreH10 : (line < n_pre)) (PreH11 : (x = (Znth (line) (last_numbers) ((0 : Int))))) (PreH12 : (x ≠ 1)) (PreH13 : (target = (Znth (line) (items) ((@List.nil Int))))) (PreH14 : (1 <= depth)) (PreH15 : (depth <= line)) (PreH16 : (depth = (Zlength (active)))) (PreH17 : (PopTarget active target x)) (PreH18 : (BoundedItem n_pre active)) (PreH19 : (total = (Zlength (flat_data)))) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= (line * n_pre))) (PreH22 : (FlatPrefix items line flat_data)) (PreH23 : (LengthsPrefix items line lengths_data)) (PreH24 : ((Zlength (cells)) = 1005)) (PreH25 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int))))))) (PreH26 : ((Znth (depth - 1) cells __default__App_option_Z) = (Some ((Znth (depth - 1) active (0 : Int)))))) ,
  ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "flat" ) )) # Ptr |-> (flat_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "line" ) )) # Int |-> (line))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "depth" ) )) # Int |-> (depth))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full values_pre n_pre last_numbers)
  ** (((( &( "stack" ) ) + ((depth - 1) * sizeof(INT)))) # Int |-> ((Znth (depth - 1) active (0 : Int))))
  ** (intArray.mixed_missing_i ( &( "stack" ) ) (depth - 1) (0 : Int) 1005 cells)
  ** (intArray.seg flat_pre (0 : Int) total flat_data)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) line lengths_data)
  ** (intArray.undef_seg lengths_pre line n_pre)
|--
  “ ((INT_MIN) <= ((Znth (depth - 1) active (0 : Int)) + 1)) ”

noncomputable def solver_safety_wit_8 : Prop :=
  forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (cells : (List (Option Int))) (lengths_data : (List Int)) (flat_data : (List Int)) (total : Int) (active : (List Int)) (depth : Int) (target : (List Int)) (x : Int) (line : Int) (items : (List (List Int))) (__default__App_option_Z : _App_option_Z) (PreH1 : (depth ≠ (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (last_numbers)))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH6 : (Pre last_numbers)) (PreH7 : (Spec last_numbers items)) (PreH8 : ((Zlength (items)) = n_pre)) (PreH9 : ((0 : Int) < line)) (PreH10 : (line < n_pre)) (PreH11 : (x = (Znth (line) (last_numbers) ((0 : Int))))) (PreH12 : (x ≠ 1)) (PreH13 : (target = (Znth (line) (items) ((@List.nil Int))))) (PreH14 : (1 <= depth)) (PreH15 : (depth <= line)) (PreH16 : (depth = (Zlength (active)))) (PreH17 : (PopTarget active target x)) (PreH18 : (BoundedItem n_pre active)) (PreH19 : (total = (Zlength (flat_data)))) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= (line * n_pre))) (PreH22 : (FlatPrefix items line flat_data)) (PreH23 : (LengthsPrefix items line lengths_data)) (PreH24 : ((Zlength (cells)) = 1005)) (PreH25 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int))))))) (PreH26 : ((Znth (depth - 1) cells __default__App_option_Z) = (Some ((Znth (depth - 1) active (0 : Int)))))) ,
  ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "flat" ) )) # Ptr |-> (flat_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "line" ) )) # Int |-> (line))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "depth" ) )) # Int |-> (depth))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full values_pre n_pre last_numbers)
  ** (((( &( "stack" ) ) + ((depth - 1) * sizeof(INT)))) # Int |-> ((Znth (depth - 1) active (0 : Int))))
  ** (intArray.mixed_missing_i ( &( "stack" ) ) (depth - 1) (0 : Int) 1005 cells)
  ** (intArray.seg flat_pre (0 : Int) total flat_data)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) line lengths_data)
  ** (intArray.undef_seg lengths_pre line n_pre)
|--
  “ ((depth - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (depth - 1)) ”

noncomputable def solver_safety_wit_9 : Prop :=
  forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (cells : (List (Option Int))) (lengths_data : (List Int)) (flat_data : (List Int)) (total : Int) (active : (List Int)) (depth : Int) (target : (List Int)) (x : Int) (line : Int) (items : (List (List Int))) (__default__App_option_Z : _App_option_Z) (PreH1 : (depth ≠ (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (last_numbers)))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH6 : (Pre last_numbers)) (PreH7 : (Spec last_numbers items)) (PreH8 : ((Zlength (items)) = n_pre)) (PreH9 : ((0 : Int) < line)) (PreH10 : (line < n_pre)) (PreH11 : (x = (Znth (line) (last_numbers) ((0 : Int))))) (PreH12 : (x ≠ 1)) (PreH13 : (target = (Znth (line) (items) ((@List.nil Int))))) (PreH14 : (1 <= depth)) (PreH15 : (depth <= line)) (PreH16 : (depth = (Zlength (active)))) (PreH17 : (PopTarget active target x)) (PreH18 : (BoundedItem n_pre active)) (PreH19 : (total = (Zlength (flat_data)))) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= (line * n_pre))) (PreH22 : (FlatPrefix items line flat_data)) (PreH23 : (LengthsPrefix items line lengths_data)) (PreH24 : ((Zlength (cells)) = 1005)) (PreH25 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int))))))) (PreH26 : ((Znth (depth - 1) cells __default__App_option_Z) = (Some ((Znth (depth - 1) active (0 : Int)))))) ,
  ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "flat" ) )) # Ptr |-> (flat_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "line" ) )) # Int |-> (line))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "depth" ) )) # Int |-> (depth))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full values_pre n_pre last_numbers)
  ** (((( &( "stack" ) ) + ((depth - 1) * sizeof(INT)))) # Int |-> ((Znth (depth - 1) active (0 : Int))))
  ** (intArray.mixed_missing_i ( &( "stack" ) ) (depth - 1) (0 : Int) 1005 cells)
  ** (intArray.seg flat_pre (0 : Int) total flat_data)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) line lengths_data)
  ** (intArray.undef_seg lengths_pre line n_pre)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_10 : Prop :=
  forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (cells : (List (Option Int))) (lengths_data : (List Int)) (flat_data : (List Int)) (total : Int) (active : (List Int)) (depth : Int) (target : (List Int)) (x : Int) (line : Int) (items : (List (List Int))) (__default__App_option_Z : _App_option_Z) (PreH1 : (depth ≠ (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (last_numbers)))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH6 : (Pre last_numbers)) (PreH7 : (Spec last_numbers items)) (PreH8 : ((Zlength (items)) = n_pre)) (PreH9 : ((0 : Int) < line)) (PreH10 : (line < n_pre)) (PreH11 : (x = (Znth (line) (last_numbers) ((0 : Int))))) (PreH12 : (x ≠ 1)) (PreH13 : (target = (Znth (line) (items) ((@List.nil Int))))) (PreH14 : (1 <= depth)) (PreH15 : (depth <= line)) (PreH16 : (depth = (Zlength (active)))) (PreH17 : (PopTarget active target x)) (PreH18 : (BoundedItem n_pre active)) (PreH19 : (total = (Zlength (flat_data)))) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= (line * n_pre))) (PreH22 : (FlatPrefix items line flat_data)) (PreH23 : (LengthsPrefix items line lengths_data)) (PreH24 : ((Zlength (cells)) = 1005)) (PreH25 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int))))))) (PreH26 : ((Znth (depth - 1) cells __default__App_option_Z) = (Some ((Znth (depth - 1) active (0 : Int)))))) ,
  ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "flat" ) )) # Ptr |-> (flat_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "line" ) )) # Int |-> (line))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "depth" ) )) # Int |-> (depth))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full values_pre n_pre last_numbers)
  ** (((( &( "stack" ) ) + ((depth - 1) * sizeof(INT)))) # Int |-> ((Znth (depth - 1) active (0 : Int))))
  ** (intArray.mixed_missing_i ( &( "stack" ) ) (depth - 1) (0 : Int) 1005 cells)
  ** (intArray.seg flat_pre (0 : Int) total flat_data)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) line lengths_data)
  ** (intArray.undef_seg lengths_pre line n_pre)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_11 : Prop :=
  forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (cells : (List (Option Int))) (lengths_data : (List Int)) (flat_data : (List Int)) (total : Int) (active : (List Int)) (depth : Int) (target : (List Int)) (x : Int) (line : Int) (items : (List (List Int))) (__default__App_option_Z : _App_option_Z) (PreH1 : (depth = (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (last_numbers)))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH6 : (Pre last_numbers)) (PreH7 : (Spec last_numbers items)) (PreH8 : ((Zlength (items)) = n_pre)) (PreH9 : ((0 : Int) < line)) (PreH10 : (line < n_pre)) (PreH11 : (x = (Znth (line) (last_numbers) ((0 : Int))))) (PreH12 : (x ≠ 1)) (PreH13 : (target = (Znth (line) (items) ((@List.nil Int))))) (PreH14 : (1 <= depth)) (PreH15 : (depth <= line)) (PreH16 : (depth = (Zlength (active)))) (PreH17 : (PopTarget active target x)) (PreH18 : (BoundedItem n_pre active)) (PreH19 : (total = (Zlength (flat_data)))) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= (line * n_pre))) (PreH22 : (FlatPrefix items line flat_data)) (PreH23 : (LengthsPrefix items line lengths_data)) (PreH24 : ((Zlength (cells)) = 1005)) (PreH25 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int))))))) (PreH26 : ((Znth (depth - 1) cells __default__App_option_Z) = (Some ((Znth (depth - 1) active (0 : Int)))))) ,
  ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "flat" ) )) # Ptr |-> (flat_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "line" ) )) # Int |-> (line))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "depth" ) )) # Int |-> (depth))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full values_pre n_pre last_numbers)
  ** (((( &( "stack" ) ) + ((depth - 1) * sizeof(INT)))) # Int |-> ((Znth (depth - 1) active (0 : Int))))
  ** (intArray.mixed_missing_i ( &( "stack" ) ) (depth - 1) (0 : Int) 1005 cells)
  ** (intArray.seg flat_pre (0 : Int) total flat_data)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) line lengths_data)
  ** (intArray.undef_seg lengths_pre line n_pre)
|--
  “ False ”

noncomputable def solver_safety_wit_12 : Prop :=
  forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (cells : (List (Option Int))) (lengths_data : (List Int)) (flat_data : (List Int)) (total : Int) (active : (List Int)) (depth : Int) (target : (List Int)) (x : Int) (line : Int) (items : (List (List Int))) (__default__App_option_Z : _App_option_Z) (PreH1 : (((Znth (depth - 1) active (0 : Int)) + 1) ≠ x)) (PreH2 : (depth ≠ (0 : Int))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (n_pre = (Zlength (last_numbers)))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH7 : (Pre last_numbers)) (PreH8 : (Spec last_numbers items)) (PreH9 : ((Zlength (items)) = n_pre)) (PreH10 : ((0 : Int) < line)) (PreH11 : (line < n_pre)) (PreH12 : (x = (Znth (line) (last_numbers) ((0 : Int))))) (PreH13 : (x ≠ 1)) (PreH14 : (target = (Znth (line) (items) ((@List.nil Int))))) (PreH15 : (1 <= depth)) (PreH16 : (depth <= line)) (PreH17 : (depth = (Zlength (active)))) (PreH18 : (PopTarget active target x)) (PreH19 : (BoundedItem n_pre active)) (PreH20 : (total = (Zlength (flat_data)))) (PreH21 : ((0 : Int) <= total)) (PreH22 : (total <= (line * n_pre))) (PreH23 : (FlatPrefix items line flat_data)) (PreH24 : (LengthsPrefix items line lengths_data)) (PreH25 : ((Zlength (cells)) = 1005)) (PreH26 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int))))))) (PreH27 : ((Znth (depth - 1) cells __default__App_option_Z) = (Some ((Znth (depth - 1) active (0 : Int)))))) ,
  ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "flat" ) )) # Ptr |-> (flat_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "line" ) )) # Int |-> (line))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "depth" ) )) # Int |-> (depth))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full values_pre n_pre last_numbers)
  ** (((( &( "stack" ) ) + ((depth - 1) * sizeof(INT)))) # Int |-> ((Znth (depth - 1) active (0 : Int))))
  ** (intArray.mixed_missing_i ( &( "stack" ) ) (depth - 1) (0 : Int) 1005 cells)
  ** (intArray.seg flat_pre (0 : Int) total flat_data)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) line lengths_data)
  ** (intArray.undef_seg lengths_pre line n_pre)
|--
  “ ((depth - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (depth - 1)) ”

noncomputable def solver_safety_wit_13 : Prop :=
  forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (cells : (List (Option Int))) (lengths_data : (List Int)) (flat_data : (List Int)) (total : Int) (active : (List Int)) (depth : Int) (target : (List Int)) (x : Int) (line : Int) (items : (List (List Int))) (__default__App_option_Z : _App_option_Z) (PreH1 : (((Znth (depth - 1) active (0 : Int)) + 1) = x)) (PreH2 : (depth ≠ (0 : Int))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (n_pre = (Zlength (last_numbers)))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH7 : (Pre last_numbers)) (PreH8 : (Spec last_numbers items)) (PreH9 : ((Zlength (items)) = n_pre)) (PreH10 : ((0 : Int) < line)) (PreH11 : (line < n_pre)) (PreH12 : (x = (Znth (line) (last_numbers) ((0 : Int))))) (PreH13 : (x ≠ 1)) (PreH14 : (target = (Znth (line) (items) ((@List.nil Int))))) (PreH15 : (1 <= depth)) (PreH16 : (depth <= line)) (PreH17 : (depth = (Zlength (active)))) (PreH18 : (PopTarget active target x)) (PreH19 : (BoundedItem n_pre active)) (PreH20 : (total = (Zlength (flat_data)))) (PreH21 : ((0 : Int) <= total)) (PreH22 : (total <= (line * n_pre))) (PreH23 : (FlatPrefix items line flat_data)) (PreH24 : (LengthsPrefix items line lengths_data)) (PreH25 : ((Zlength (cells)) = 1005)) (PreH26 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int))))))) (PreH27 : ((Znth (depth - 1) cells __default__App_option_Z) = (Some ((Znth (depth - 1) active (0 : Int)))))) ,
  ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "flat" ) )) # Ptr |-> (flat_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "line" ) )) # Int |-> (line))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "depth" ) )) # Int |-> (depth))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full values_pre n_pre last_numbers)
  ** (((( &( "stack" ) ) + ((depth - 1) * sizeof(INT)))) # Int |-> ((Znth (depth - 1) active (0 : Int))))
  ** (intArray.mixed_missing_i ( &( "stack" ) ) (depth - 1) (0 : Int) 1005 cells)
  ** (intArray.seg flat_pre (0 : Int) total flat_data)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) line lengths_data)
  ** (intArray.undef_seg lengths_pre line n_pre)
|--
  “ ((depth - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (depth - 1)) ”

noncomputable def solver_safety_wit_14 : Prop :=
  forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (cells : (List (Option Int))) (lengths_data : (List Int)) (flat_data : (List Int)) (total : Int) (active : (List Int)) (depth : Int) (target : (List Int)) (x : Int) (line : Int) (items : (List (List Int))) (__default__App_option_Z : _App_option_Z) (PreH1 : (((Znth (depth - 1) active (0 : Int)) + 1) = x)) (PreH2 : (depth ≠ (0 : Int))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (n_pre = (Zlength (last_numbers)))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH7 : (Pre last_numbers)) (PreH8 : (Spec last_numbers items)) (PreH9 : ((Zlength (items)) = n_pre)) (PreH10 : ((0 : Int) < line)) (PreH11 : (line < n_pre)) (PreH12 : (x = (Znth (line) (last_numbers) ((0 : Int))))) (PreH13 : (x ≠ 1)) (PreH14 : (target = (Znth (line) (items) ((@List.nil Int))))) (PreH15 : (1 <= depth)) (PreH16 : (depth <= line)) (PreH17 : (depth = (Zlength (active)))) (PreH18 : (PopTarget active target x)) (PreH19 : (BoundedItem n_pre active)) (PreH20 : (total = (Zlength (flat_data)))) (PreH21 : ((0 : Int) <= total)) (PreH22 : (total <= (line * n_pre))) (PreH23 : (FlatPrefix items line flat_data)) (PreH24 : (LengthsPrefix items line lengths_data)) (PreH25 : ((Zlength (cells)) = 1005)) (PreH26 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int))))))) (PreH27 : ((Znth (depth - 1) cells __default__App_option_Z) = (Some ((Znth (depth - 1) active (0 : Int)))))) ,
  ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "flat" ) )) # Ptr |-> (flat_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "line" ) )) # Int |-> (line))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "depth" ) )) # Int |-> (depth))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full values_pre n_pre last_numbers)
  ** (((( &( "stack" ) ) + ((depth - 1) * sizeof(INT)))) # Int |-> ((Znth (depth - 1) active (0 : Int))))
  ** (intArray.mixed_missing_i ( &( "stack" ) ) (depth - 1) (0 : Int) 1005 cells)
  ** (intArray.seg flat_pre (0 : Int) total flat_data)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) line lengths_data)
  ** (intArray.undef_seg lengths_pre line n_pre)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_15 : Prop :=
  forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (items : (List (List Int))) (cells : (List (Option Int))) (active : (List Int)) (flat_data : (List Int)) (lengths_data : (List Int)) (line : Int) (depth : Int) (total : Int) (__default__App_option_Z : _App_option_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (n_pre = (Zlength (last_numbers)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH5 : (Pre last_numbers)) (PreH6 : (Spec last_numbers items)) (PreH7 : ((Zlength (items)) = n_pre)) (PreH8 : ((0 : Int) <= line)) (PreH9 : (line < n_pre)) (PreH10 : (active = (Znth (line) (items) ((@List.nil Int))))) (PreH11 : (1 <= depth)) (PreH12 : (depth <= (line + 1))) (PreH13 : (depth = (Zlength (active)))) (PreH14 : (BoundedItem n_pre active)) (PreH15 : (total = (Zlength (flat_data)))) (PreH16 : ((0 : Int) <= total)) (PreH17 : (total <= (line * n_pre))) (PreH18 : (FlatPrefix items line flat_data)) (PreH19 : (LengthsPrefix items line lengths_data)) (PreH20 : ((Zlength (cells)) = 1005)) (PreH21 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int))))))) ,
  ((( &( "i" ) )) # Int |->_)
  ** (intArray.seg lengths_pre (0 : Int) (line + 1) (lengths_data ++ (depth :: (@List.nil Int))))
  ** (intArray.undef_seg lengths_pre (line + 1) n_pre)
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "flat" ) )) # Ptr |-> (flat_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "line" ) )) # Int |-> (line))
  ** ((( &( "depth" ) )) # Int |-> (depth))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "x" ) )) # Int |->_)
  ** (intArray.full values_pre n_pre last_numbers)
  ** (intArray.mixed_full ( &( "stack" ) ) 1005 cells)
  ** (intArray.seg flat_pre (0 : Int) total flat_data)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_16 : Prop :=
  forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (items : (List (List Int))) (cells : (List (Option Int))) (active : (List Int)) (flat_before : (List Int)) (flat_data : (List Int)) (lengths_data : (List Int)) (line : Int) (depth : Int) (i : Int) (total : Int) (__default__App_option_Z : _App_option_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (n_pre = (Zlength (last_numbers)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH5 : (Pre last_numbers)) (PreH6 : (Spec last_numbers items)) (PreH7 : ((Zlength (items)) = n_pre)) (PreH8 : ((0 : Int) <= line)) (PreH9 : (line < n_pre)) (PreH10 : (active = (Znth (line) (items) ((@List.nil Int))))) (PreH11 : (1 <= depth)) (PreH12 : (depth <= (line + 1))) (PreH13 : ((line + 1) <= n_pre)) (PreH14 : (depth = (Zlength (active)))) (PreH15 : (BoundedItem n_pre active)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < depth)) (PreH18 : (FlatPrefix items line flat_before)) (PreH19 : (flat_data = (flat_before ++ (sublist ((0 : Int)) (i) (active))))) (PreH20 : (total = (Zlength (flat_data)))) (PreH21 : ((0 : Int) <= total)) (PreH22 : ((total + (depth - i)) <= ((line + 1) * n_pre))) (PreH23 : (((line + 1) * n_pre) <= (n_pre * n_pre))) (PreH24 : (LengthsPrefix items (line + 1) lengths_data)) (PreH25 : ((Zlength (cells)) = 1005)) (PreH26 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int))))))) (PreH27 : ((Znth i cells __default__App_option_Z) = (Some ((Znth i active (0 : Int)))))) ,
  (intArray.seg flat_pre (0 : Int) (total + 1) (flat_data ++ ((Znth i active (0 : Int)) :: (@List.nil Int))))
  ** (intArray.mixed_full ( &( "stack" ) ) 1005 cells)
  ** (intArray.undef_seg flat_pre (total + 1) (n_pre * n_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "flat" ) )) # Ptr |-> (flat_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "line" ) )) # Int |-> (line))
  ** ((( &( "depth" ) )) # Int |-> (depth))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** ((( &( "x" ) )) # Int |->_)
  ** (intArray.full values_pre n_pre last_numbers)
  ** (intArray.seg lengths_pre (0 : Int) (line + 1) lengths_data)
  ** (intArray.undef_seg lengths_pre (line + 1) n_pre)
|--
  “ ((total + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (total + 1)) ”

noncomputable def solver_safety_wit_17 : Prop :=
  forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (items : (List (List Int))) (cells : (List (Option Int))) (active : (List Int)) (flat_before : (List Int)) (flat_data : (List Int)) (lengths_data : (List Int)) (line : Int) (depth : Int) (i : Int) (total : Int) (__default__App_option_Z : _App_option_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (n_pre = (Zlength (last_numbers)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH5 : (Pre last_numbers)) (PreH6 : (Spec last_numbers items)) (PreH7 : ((Zlength (items)) = n_pre)) (PreH8 : ((0 : Int) <= line)) (PreH9 : (line < n_pre)) (PreH10 : (active = (Znth (line) (items) ((@List.nil Int))))) (PreH11 : (1 <= depth)) (PreH12 : (depth <= (line + 1))) (PreH13 : ((line + 1) <= n_pre)) (PreH14 : (depth = (Zlength (active)))) (PreH15 : (BoundedItem n_pre active)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < depth)) (PreH18 : (FlatPrefix items line flat_before)) (PreH19 : (flat_data = (flat_before ++ (sublist ((0 : Int)) (i) (active))))) (PreH20 : (total = (Zlength (flat_data)))) (PreH21 : ((0 : Int) <= total)) (PreH22 : ((total + (depth - i)) <= ((line + 1) * n_pre))) (PreH23 : (((line + 1) * n_pre) <= (n_pre * n_pre))) (PreH24 : (LengthsPrefix items (line + 1) lengths_data)) (PreH25 : ((Zlength (cells)) = 1005)) (PreH26 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int))))))) (PreH27 : ((Znth i cells __default__App_option_Z) = (Some ((Znth i active (0 : Int)))))) ,
  (intArray.seg flat_pre (0 : Int) (total + 1) (flat_data ++ ((Znth i active (0 : Int)) :: (@List.nil Int))))
  ** (intArray.mixed_full ( &( "stack" ) ) 1005 cells)
  ** (intArray.undef_seg flat_pre (total + 1) (n_pre * n_pre))
  ** ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "flat" ) )) # Ptr |-> (flat_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "line" ) )) # Int |-> (line))
  ** ((( &( "depth" ) )) # Int |-> (depth))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "total" ) )) # Int |-> ((total + 1)))
  ** ((( &( "x" ) )) # Int |->_)
  ** (intArray.full values_pre n_pre last_numbers)
  ** (intArray.seg lengths_pre (0 : Int) (line + 1) lengths_data)
  ** (intArray.undef_seg lengths_pre (line + 1) n_pre)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_18 : Prop :=
  forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (cells : (List (Option Int))) (lengths_data : (List Int)) (total : Int) (flat_data : (List Int)) (flat_before : (List Int)) (i : Int) (depth : Int) (active : (List Int)) (line : Int) (items : (List (List Int))) (__default__App_option_Z : _App_option_Z) (PreH1 : (i >= depth)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (last_numbers)))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH6 : (Pre last_numbers)) (PreH7 : (Spec last_numbers items)) (PreH8 : ((Zlength (items)) = n_pre)) (PreH9 : ((0 : Int) <= line)) (PreH10 : (line < n_pre)) (PreH11 : (active = (Znth (line) (items) ((@List.nil Int))))) (PreH12 : (1 <= depth)) (PreH13 : (depth <= (line + 1))) (PreH14 : ((line + 1) <= n_pre)) (PreH15 : (depth = (Zlength (active)))) (PreH16 : (BoundedItem n_pre active)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i <= depth)) (PreH19 : (FlatPrefix items line flat_before)) (PreH20 : (flat_data = (flat_before ++ (sublist ((0 : Int)) (i) (active))))) (PreH21 : (total = (Zlength (flat_data)))) (PreH22 : ((0 : Int) <= total)) (PreH23 : ((total + (depth - i)) <= ((line + 1) * n_pre))) (PreH24 : (((line + 1) * n_pre) <= (n_pre * n_pre))) (PreH25 : (LengthsPrefix items (line + 1) lengths_data)) (PreH26 : ((Zlength (cells)) = 1005)) (PreH27 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int))))))) ,
  ((( &( "values" ) )) # Ptr |-> (values_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "flat" ) )) # Ptr |-> (flat_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "line" ) )) # Int |-> (line))
  ** ((( &( "depth" ) )) # Int |-> (depth))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full values_pre n_pre last_numbers)
  ** (intArray.mixed_full ( &( "stack" ) ) 1005 cells)
  ** (intArray.seg flat_pre (0 : Int) total flat_data)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) (line + 1) lengths_data)
  ** (intArray.undef_seg lengths_pre (line + 1) n_pre)
|--
  “ ((line + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (line + 1)) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (__default__App_option_Z : _App_option_Z) (PreH1 : (1 <= (Zlength (last_numbers)))) (PreH2 : ((Zlength (last_numbers)) <= 1000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (last_numbers)))) -> ((1 <= (Znth i last_numbers (0 : Int))) ∧ ((Znth i last_numbers (0 : Int)) <= (Zlength (last_numbers)))))) (PreH4 : (Pre last_numbers)) (PreH5 : (n_pre = (Zlength (last_numbers)))) ,
  (intArray.undef_full ( &( "stack" ) ) 1005)
  ** (intArray.full values_pre n_pre last_numbers)
  ** (intArray.undef_full flat_pre (n_pre * n_pre))
  ** (intArray.undef_full lengths_pre n_pre)
|--
  EX cells : (List (Option Int)), EX lengths_data : (List Int), EX flat_data : (List Int), EX active : (List Int), EX items : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (n_pre = (Zlength (last_numbers))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre))) ” &&
  “ (Pre last_numbers) ” &&
  “ (Spec last_numbers items) ” &&
  “ ((Zlength (items)) = n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) = (Zlength (active))) ” &&
  “ (CurrentItem items (0 : Int) active) ” &&
  “ (BoundedItem n_pre active) ” &&
  “ ((0 : Int) = (Zlength (flat_data))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= ((0 : Int) * n_pre)) ” &&
  “ (FlatPrefix items (0 : Int) flat_data) ” &&
  “ (LengthsPrefix items (0 : Int) lengths_data) ” &&
  “ ((Zlength (cells)) = 1005) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (0 : Int))) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int)))))) ”
  &&  (intArray.full values_pre n_pre last_numbers)
  ** (intArray.mixed_full ( &( "stack" ) ) 1005 cells)
  ** (intArray.seg flat_pre (0 : Int) (0 : Int) flat_data)
  ** (intArray.undef_seg flat_pre (0 : Int) (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) (0 : Int) lengths_data)
  ** (intArray.undef_seg lengths_pre (0 : Int) n_pre)
) \/
(
forall (n_pre : Int) (last_numbers : (List Int)) (__default__App_option_Z : _App_option_Z) (PreH1 : (1 <= (Zlength (last_numbers)))) (PreH2 : ((Zlength (last_numbers)) <= 1000)) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < (Zlength (last_numbers)))) -> ((1 <= (Znth i last_numbers (0 : Int))) ∧ ((Znth i last_numbers (0 : Int)) <= (Zlength (last_numbers)))))) (PreH4 : (Pre last_numbers)) (PreH5 : (n_pre = (Zlength (last_numbers)))) ,
  (intArray.undef_full ( &( "stack" ) ) 1005)
|--
  EX cells : (List (Option Int)), EX active : (List Int), EX items : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (n_pre = (Zlength (last_numbers))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre))) ” &&
  “ (Pre last_numbers) ” &&
  “ (Spec last_numbers items) ” &&
  “ ((Zlength (items)) = n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) = (Zlength (active))) ” &&
  “ (CurrentItem items (0 : Int) active) ” &&
  “ (BoundedItem n_pre active) ” &&
  “ ((0 : Int) = (Zlength ((@List.nil Int)))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= ((0 : Int) * n_pre)) ” &&
  “ (FlatPrefix items (0 : Int) (@List.nil Int)) ” &&
  “ (LengthsPrefix items (0 : Int) (@List.nil Int)) ” &&
  “ ((Zlength (cells)) = 1005) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (0 : Int))) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int)))))) ”
  &&  (intArray.mixed_full ( &( "stack" ) ) 1005 cells)
)

noncomputable def solver_entail_wit_2 : Prop :=
  (
forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (cells_2 : (List (Option Int))) (lengths_data_2 : (List Int)) (flat_data_2 : (List Int)) (total : Int) (active_2 : (List Int)) (depth : Int) (line : Int) (items_2 : (List (List Int))) (__default__App_option_Z : _App_option_Z) (PreH1 : ((Znth line last_numbers (0 : Int)) ≠ 1)) (PreH2 : (line < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (n_pre = (Zlength (last_numbers)))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth (k_3) (last_numbers) ((0 : Int)))) ∧ ((Znth (k_3) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH7 : (Pre last_numbers)) (PreH8 : (Spec last_numbers items_2)) (PreH9 : ((Zlength (items_2)) = n_pre)) (PreH10 : ((0 : Int) <= line)) (PreH11 : (line <= n_pre)) (PreH12 : ((0 : Int) <= depth)) (PreH13 : (depth <= line)) (PreH14 : (depth = (Zlength (active_2)))) (PreH15 : (CurrentItem items_2 line active_2)) (PreH16 : (BoundedItem n_pre active_2)) (PreH17 : (total = (Zlength (flat_data_2)))) (PreH18 : ((0 : Int) <= total)) (PreH19 : (total <= (line * n_pre))) (PreH20 : (FlatPrefix items_2 line flat_data_2)) (PreH21 : (LengthsPrefix items_2 line lengths_data_2)) (PreH22 : ((Zlength (cells_2)) = 1005)) (PreH23 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < depth)) -> ((Znth k_4 cells_2 __default__App_option_Z) = (Some ((Znth k_4 active_2 (0 : Int))))))) ,
  (intArray.full values_pre n_pre last_numbers)
  ** (intArray.mixed_full ( &( "stack" ) ) 1005 cells_2)
  ** (intArray.seg flat_pre (0 : Int) total flat_data_2)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) line lengths_data_2)
  ** (intArray.undef_seg lengths_pre line n_pre)
|--
  EX cells : (List (Option Int)), EX lengths_data : (List Int), EX flat_data : (List Int), EX active : (List Int), EX target : (List Int), EX items : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (n_pre = (Zlength (last_numbers))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre))) ” &&
  “ (Pre last_numbers) ” &&
  “ (Spec last_numbers items) ” &&
  “ ((Zlength (items)) = n_pre) ” &&
  “ ((0 : Int) < line) ” &&
  “ (line < n_pre) ” &&
  “ ((Znth line last_numbers (0 : Int)) = (Znth (line) (last_numbers) ((0 : Int)))) ” &&
  “ ((Znth line last_numbers (0 : Int)) ≠ 1) ” &&
  “ (target = (Znth (line) (items) ((@List.nil Int)))) ” &&
  “ (1 <= depth) ” &&
  “ (depth <= line) ” &&
  “ (depth = (Zlength (active))) ” &&
  “ (PopTarget active target (Znth line last_numbers (0 : Int))) ” &&
  “ (BoundedItem n_pre active) ” &&
  “ (total = (Zlength (flat_data))) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= (line * n_pre)) ” &&
  “ (FlatPrefix items line flat_data) ” &&
  “ (LengthsPrefix items line lengths_data) ” &&
  “ ((Zlength (cells)) = 1005) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int)))))) ” &&
  “ ((Znth (depth - 1) cells __default__App_option_Z) = (Some ((Znth (depth - 1) active (0 : Int))))) ”
  &&  (intArray.full values_pre n_pre last_numbers)
  ** (((( &( "stack" ) ) + ((depth - 1) * sizeof(INT)))) # Int |-> ((Znth (depth - 1) active (0 : Int))))
  ** (intArray.mixed_missing_i ( &( "stack" ) ) (depth - 1) (0 : Int) 1005 cells)
  ** (intArray.seg flat_pre (0 : Int) total flat_data)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) line lengths_data)
  ** (intArray.undef_seg lengths_pre line n_pre)
) \/
(
forall (n_pre : Int) (last_numbers : (List Int)) (cells_2 : (List (Option Int))) (lengths_data_2 : (List Int)) (flat_data_2 : (List Int)) (total : Int) (active_2 : (List Int)) (depth : Int) (line : Int) (items_2 : (List (List Int))) (__default__App_option_Z : _App_option_Z) (PreH1 : ((Znth line last_numbers (0 : Int)) ≠ 1)) (PreH2 : (line < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (n_pre = (Zlength (last_numbers)))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth (k_3) (last_numbers) ((0 : Int)))) ∧ ((Znth (k_3) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH7 : (Pre last_numbers)) (PreH8 : (Spec last_numbers items_2)) (PreH9 : ((Zlength (items_2)) = n_pre)) (PreH10 : ((0 : Int) <= line)) (PreH11 : (line <= n_pre)) (PreH12 : ((0 : Int) <= depth)) (PreH13 : (depth <= line)) (PreH14 : (depth = (Zlength (active_2)))) (PreH15 : (CurrentItem items_2 line active_2)) (PreH16 : (BoundedItem n_pre active_2)) (PreH17 : (total = (Zlength (flat_data_2)))) (PreH18 : ((0 : Int) <= total)) (PreH19 : (total <= (line * n_pre))) (PreH20 : (FlatPrefix items_2 line flat_data_2)) (PreH21 : (LengthsPrefix items_2 line lengths_data_2)) (PreH22 : ((Zlength (cells_2)) = 1005)) (PreH23 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < depth)) -> ((Znth k_4 cells_2 __default__App_option_Z) = (Some ((Znth k_4 active_2 (0 : Int))))))) ,
  (intArray.mixed_full ( &( "stack" ) ) 1005 cells_2)
|--
  EX cells : (List (Option Int)), EX active : (List Int), EX items : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (n_pre = (Zlength (last_numbers))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre))) ” &&
  “ (Pre last_numbers) ” &&
  “ (Spec last_numbers items) ” &&
  “ ((Zlength (items)) = n_pre) ” &&
  “ ((0 : Int) < line) ” &&
  “ (line < n_pre) ” &&
  “ ((Znth line last_numbers (0 : Int)) = (Znth (line) (last_numbers) ((0 : Int)))) ” &&
  “ ((Znth line last_numbers (0 : Int)) ≠ 1) ” &&
  “ (1 <= depth) ” &&
  “ (depth <= line) ” &&
  “ (depth = (Zlength (active))) ” &&
  “ (PopTarget active (Znth (line) (items) ((@List.nil Int))) (Znth line last_numbers (0 : Int))) ” &&
  “ (BoundedItem n_pre active) ” &&
  “ (total = (Zlength (flat_data_2))) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= (line * n_pre)) ” &&
  “ (FlatPrefix items line flat_data_2) ” &&
  “ (LengthsPrefix items line lengths_data_2) ” &&
  “ ((Zlength (cells)) = 1005) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int)))))) ” &&
  “ ((Znth (depth - 1) cells __default__App_option_Z) = (Some ((Znth (depth - 1) active (0 : Int))))) ”
  &&  (((( &( "stack" ) ) + ((depth - 1) * sizeof(INT)))) # Int |-> ((Znth (depth - 1) active (0 : Int))))
  ** (intArray.mixed_missing_i ( &( "stack" ) ) (depth - 1) (0 : Int) 1005 cells)
)

noncomputable def solver_entail_wit_3_1 : Prop :=
  forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (cells : (List (Option Int))) (lengths_data : (List Int)) (flat_data : (List Int)) (total : Int) (active : (List Int)) (depth : Int) (target : (List Int)) (x : Int) (line : Int) (items : (List (List Int))) (__default__App_option_Z : _App_option_Z) (PreH1 : (depth = (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (last_numbers)))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH6 : (Pre last_numbers)) (PreH7 : (Spec last_numbers items)) (PreH8 : ((Zlength (items)) = n_pre)) (PreH9 : ((0 : Int) < line)) (PreH10 : (line < n_pre)) (PreH11 : (x = (Znth (line) (last_numbers) ((0 : Int))))) (PreH12 : (x ≠ 1)) (PreH13 : (target = (Znth (line) (items) ((@List.nil Int))))) (PreH14 : (1 <= depth)) (PreH15 : (depth <= line)) (PreH16 : (depth = (Zlength (active)))) (PreH17 : (PopTarget active target x)) (PreH18 : (BoundedItem n_pre active)) (PreH19 : (total = (Zlength (flat_data)))) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= (line * n_pre))) (PreH22 : (FlatPrefix items line flat_data)) (PreH23 : (LengthsPrefix items line lengths_data)) (PreH24 : ((Zlength (cells)) = 1005)) (PreH25 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int))))))) (PreH26 : ((Znth (depth - 1) cells __default__App_option_Z) = (Some ((Znth (depth - 1) active (0 : Int)))))) ,
  (intArray.full values_pre n_pre last_numbers)
  ** (((( &( "stack" ) ) + ((depth - 1) * sizeof(INT)))) # Int |-> ((Znth (depth - 1) active (0 : Int))))
  ** (intArray.mixed_missing_i ( &( "stack" ) ) (depth - 1) (0 : Int) 1005 cells)
  ** (intArray.seg flat_pre (0 : Int) total flat_data)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) line lengths_data)
  ** (intArray.undef_seg lengths_pre line n_pre)
|--
  “ (((Znth (depth - 1) active (0 : Int)) + 1) = x) ” &&
  “ (depth ≠ (0 : Int)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (n_pre = (Zlength (last_numbers))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre))) ” &&
  “ (Pre last_numbers) ” &&
  “ (Spec last_numbers items) ” &&
  “ ((Zlength (items)) = n_pre) ” &&
  “ ((0 : Int) < line) ” &&
  “ (line < n_pre) ” &&
  “ (x = (Znth (line) (last_numbers) ((0 : Int)))) ” &&
  “ (x ≠ 1) ” &&
  “ (target = (Znth (line) (items) ((@List.nil Int)))) ” &&
  “ (1 <= depth) ” &&
  “ (depth <= line) ” &&
  “ (depth = (Zlength (active))) ” &&
  “ (PopTarget active target x) ” &&
  “ (BoundedItem n_pre active) ” &&
  “ (total = (Zlength (flat_data))) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= (line * n_pre)) ” &&
  “ (FlatPrefix items line flat_data) ” &&
  “ (LengthsPrefix items line lengths_data) ” &&
  “ ((Zlength (cells)) = 1005) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int)))))) ” &&
  “ ((Znth (depth - 1) cells __default__App_option_Z) = (Some ((Znth (depth - 1) active (0 : Int))))) ”
  &&  (intArray.full values_pre n_pre last_numbers)
  ** (((( &( "stack" ) ) + ((depth - 1) * sizeof(INT)))) # Int |-> ((Znth (depth - 1) active (0 : Int))))
  ** (intArray.mixed_missing_i ( &( "stack" ) ) (depth - 1) (0 : Int) 1005 cells)
  ** (intArray.seg flat_pre (0 : Int) total flat_data)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) line lengths_data)
  ** (intArray.undef_seg lengths_pre line n_pre)

noncomputable def solver_entail_wit_3_2 : Prop :=
  forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (cells : (List (Option Int))) (lengths_data : (List Int)) (flat_data : (List Int)) (total : Int) (active : (List Int)) (depth : Int) (target : (List Int)) (x : Int) (line : Int) (items : (List (List Int))) (__default__App_option_Z : _App_option_Z) (PreH1 : (((Znth (depth - 1) active (0 : Int)) + 1) = x)) (PreH2 : (depth ≠ (0 : Int))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (n_pre = (Zlength (last_numbers)))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH7 : (Pre last_numbers)) (PreH8 : (Spec last_numbers items)) (PreH9 : ((Zlength (items)) = n_pre)) (PreH10 : ((0 : Int) < line)) (PreH11 : (line < n_pre)) (PreH12 : (x = (Znth (line) (last_numbers) ((0 : Int))))) (PreH13 : (x ≠ 1)) (PreH14 : (target = (Znth (line) (items) ((@List.nil Int))))) (PreH15 : (1 <= depth)) (PreH16 : (depth <= line)) (PreH17 : (depth = (Zlength (active)))) (PreH18 : (PopTarget active target x)) (PreH19 : (BoundedItem n_pre active)) (PreH20 : (total = (Zlength (flat_data)))) (PreH21 : ((0 : Int) <= total)) (PreH22 : (total <= (line * n_pre))) (PreH23 : (FlatPrefix items line flat_data)) (PreH24 : (LengthsPrefix items line lengths_data)) (PreH25 : ((Zlength (cells)) = 1005)) (PreH26 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int))))))) (PreH27 : ((Znth (depth - 1) cells __default__App_option_Z) = (Some ((Znth (depth - 1) active (0 : Int)))))) ,
  (intArray.full values_pre n_pre last_numbers)
  ** (((( &( "stack" ) ) + ((depth - 1) * sizeof(INT)))) # Int |-> ((Znth (depth - 1) active (0 : Int))))
  ** (intArray.mixed_missing_i ( &( "stack" ) ) (depth - 1) (0 : Int) 1005 cells)
  ** (intArray.seg flat_pre (0 : Int) total flat_data)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) line lengths_data)
  ** (intArray.undef_seg lengths_pre line n_pre)
|--
  “ (((Znth (depth - 1) active (0 : Int)) + 1) = x) ” &&
  “ (depth ≠ (0 : Int)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (n_pre = (Zlength (last_numbers))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre))) ” &&
  “ (Pre last_numbers) ” &&
  “ (Spec last_numbers items) ” &&
  “ ((Zlength (items)) = n_pre) ” &&
  “ ((0 : Int) < line) ” &&
  “ (line < n_pre) ” &&
  “ (x = (Znth (line) (last_numbers) ((0 : Int)))) ” &&
  “ (x ≠ 1) ” &&
  “ (target = (Znth (line) (items) ((@List.nil Int)))) ” &&
  “ (1 <= depth) ” &&
  “ (depth <= line) ” &&
  “ (depth = (Zlength (active))) ” &&
  “ (PopTarget active target x) ” &&
  “ (BoundedItem n_pre active) ” &&
  “ (total = (Zlength (flat_data))) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= (line * n_pre)) ” &&
  “ (FlatPrefix items line flat_data) ” &&
  “ (LengthsPrefix items line lengths_data) ” &&
  “ ((Zlength (cells)) = 1005) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int)))))) ” &&
  “ ((Znth (depth - 1) cells __default__App_option_Z) = (Some ((Znth (depth - 1) active (0 : Int))))) ”
  &&  (intArray.full values_pre n_pre last_numbers)
  ** (((( &( "stack" ) ) + ((depth - 1) * sizeof(INT)))) # Int |-> ((Znth (depth - 1) active (0 : Int))))
  ** (intArray.mixed_missing_i ( &( "stack" ) ) (depth - 1) (0 : Int) 1005 cells)
  ** (intArray.seg flat_pre (0 : Int) total flat_data)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) line lengths_data)
  ** (intArray.undef_seg lengths_pre line n_pre)

noncomputable def solver_entail_wit_4 : Prop :=
  (
forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (cells_2 : (List (Option Int))) (lengths_data_2 : (List Int)) (flat_data_2 : (List Int)) (total : Int) (active_2 : (List Int)) (depth : Int) (target_2 : (List Int)) (x : Int) (line : Int) (items_2 : (List (List Int))) (__default__App_option_Z : _App_option_Z) (PreH1 : (((Znth (depth - 1) active_2 (0 : Int)) + 1) ≠ x)) (PreH2 : (depth ≠ (0 : Int))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (n_pre = (Zlength (last_numbers)))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH7 : (Pre last_numbers)) (PreH8 : (Spec last_numbers items_2)) (PreH9 : ((Zlength (items_2)) = n_pre)) (PreH10 : ((0 : Int) < line)) (PreH11 : (line < n_pre)) (PreH12 : (x = (Znth (line) (last_numbers) ((0 : Int))))) (PreH13 : (x ≠ 1)) (PreH14 : (target_2 = (Znth (line) (items_2) ((@List.nil Int))))) (PreH15 : (1 <= depth)) (PreH16 : (depth <= line)) (PreH17 : (depth = (Zlength (active_2)))) (PreH18 : (PopTarget active_2 target_2 x)) (PreH19 : (BoundedItem n_pre active_2)) (PreH20 : (total = (Zlength (flat_data_2)))) (PreH21 : ((0 : Int) <= total)) (PreH22 : (total <= (line * n_pre))) (PreH23 : (FlatPrefix items_2 line flat_data_2)) (PreH24 : (LengthsPrefix items_2 line lengths_data_2)) (PreH25 : ((Zlength (cells_2)) = 1005)) (PreH26 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells_2 __default__App_option_Z) = (Some ((Znth k_2 active_2 (0 : Int))))))) (PreH27 : ((Znth (depth - 1) cells_2 __default__App_option_Z) = (Some ((Znth (depth - 1) active_2 (0 : Int)))))) ,
  (intArray.full values_pre n_pre last_numbers)
  ** (((( &( "stack" ) ) + ((depth - 1) * sizeof(INT)))) # Int |-> ((Znth (depth - 1) active_2 (0 : Int))))
  ** (intArray.mixed_missing_i ( &( "stack" ) ) (depth - 1) (0 : Int) 1005 cells_2)
  ** (intArray.seg flat_pre (0 : Int) total flat_data_2)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) line lengths_data_2)
  ** (intArray.undef_seg lengths_pre line n_pre)
|--
  EX cells : (List (Option Int)), EX lengths_data : (List Int), EX flat_data : (List Int), EX active : (List Int), EX target : (List Int), EX items : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (n_pre = (Zlength (last_numbers))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre))) ” &&
  “ (Pre last_numbers) ” &&
  “ (Spec last_numbers items) ” &&
  “ ((Zlength (items)) = n_pre) ” &&
  “ ((0 : Int) < line) ” &&
  “ (line < n_pre) ” &&
  “ (x = (Znth (line) (last_numbers) ((0 : Int)))) ” &&
  “ (x ≠ 1) ” &&
  “ (target = (Znth (line) (items) ((@List.nil Int)))) ” &&
  “ (1 <= (depth - 1)) ” &&
  “ ((depth - 1) <= line) ” &&
  “ ((depth - 1) = (Zlength (active))) ” &&
  “ (PopTarget active target x) ” &&
  “ (BoundedItem n_pre active) ” &&
  “ (total = (Zlength (flat_data))) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= (line * n_pre)) ” &&
  “ (FlatPrefix items line flat_data) ” &&
  “ (LengthsPrefix items line lengths_data) ” &&
  “ ((Zlength (cells)) = 1005) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (depth - 1))) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int)))))) ” &&
  “ ((Znth ((depth - 1) - 1) cells __default__App_option_Z) = (Some ((Znth ((depth - 1) - 1) active (0 : Int))))) ”
  &&  (intArray.full values_pre n_pre last_numbers)
  ** (((( &( "stack" ) ) + (((depth - 1) - 1) * sizeof(INT)))) # Int |-> ((Znth ((depth - 1) - 1) active (0 : Int))))
  ** (intArray.mixed_missing_i ( &( "stack" ) ) ((depth - 1) - 1) (0 : Int) 1005 cells)
  ** (intArray.seg flat_pre (0 : Int) total flat_data)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) line lengths_data)
  ** (intArray.undef_seg lengths_pre line n_pre)
) \/
(
forall (n_pre : Int) (last_numbers : (List Int)) (cells_2 : (List (Option Int))) (lengths_data_2 : (List Int)) (flat_data_2 : (List Int)) (total : Int) (active_2 : (List Int)) (depth : Int) (target_2 : (List Int)) (x : Int) (line : Int) (items_2 : (List (List Int))) (__default__App_option_Z : _App_option_Z) (PreH1 : ((Znth (depth - 1) active_2 (0 : Int)) <= INT_MAX)) (PreH2 : ((Znth (depth - 1) active_2 (0 : Int)) >= INT_MIN)) (PreH3 : (((Znth (depth - 1) active_2 (0 : Int)) + 1) ≠ x)) (PreH4 : (depth ≠ (0 : Int))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (n_pre = (Zlength (last_numbers)))) (PreH8 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH9 : (Pre last_numbers)) (PreH10 : (Spec last_numbers items_2)) (PreH11 : ((Zlength (items_2)) = n_pre)) (PreH12 : ((0 : Int) < line)) (PreH13 : (line < n_pre)) (PreH14 : (x = (Znth (line) (last_numbers) ((0 : Int))))) (PreH15 : (x ≠ 1)) (PreH16 : (target_2 = (Znth (line) (items_2) ((@List.nil Int))))) (PreH17 : (1 <= depth)) (PreH18 : (depth <= line)) (PreH19 : (depth = (Zlength (active_2)))) (PreH20 : (PopTarget active_2 target_2 x)) (PreH21 : (BoundedItem n_pre active_2)) (PreH22 : (total = (Zlength (flat_data_2)))) (PreH23 : ((0 : Int) <= total)) (PreH24 : (total <= (line * n_pre))) (PreH25 : (FlatPrefix items_2 line flat_data_2)) (PreH26 : (LengthsPrefix items_2 line lengths_data_2)) (PreH27 : ((Zlength (cells_2)) = 1005)) (PreH28 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells_2 __default__App_option_Z) = (Some ((Znth k_2 active_2 (0 : Int))))))) (PreH29 : ((Znth (depth - 1) cells_2 __default__App_option_Z) = (Some ((Znth (depth - 1) active_2 (0 : Int)))))) ,
  (((( &( "stack" ) ) + ((depth - 1) * sizeof(INT)))) # Int |-> ((Znth (depth - 1) active_2 (0 : Int))))
  ** (intArray.mixed_missing_i ( &( "stack" ) ) (depth - 1) (0 : Int) 1005 cells_2)
|--
  EX cells : (List (Option Int)), EX active : (List Int), EX items : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (n_pre = (Zlength (last_numbers))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre))) ” &&
  “ (Pre last_numbers) ” &&
  “ (Spec last_numbers items) ” &&
  “ ((Zlength (items)) = n_pre) ” &&
  “ ((0 : Int) < line) ” &&
  “ (line < n_pre) ” &&
  “ (x = (Znth (line) (last_numbers) ((0 : Int)))) ” &&
  “ (x ≠ 1) ” &&
  “ (1 <= (depth - 1)) ” &&
  “ ((depth - 1) <= line) ” &&
  “ ((depth - 1) = (Zlength (active))) ” &&
  “ (PopTarget active (Znth (line) (items) ((@List.nil Int))) x) ” &&
  “ (BoundedItem n_pre active) ” &&
  “ (total = (Zlength (flat_data_2))) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= (line * n_pre)) ” &&
  “ (FlatPrefix items line flat_data_2) ” &&
  “ (LengthsPrefix items line lengths_data_2) ” &&
  “ ((Zlength (cells)) = 1005) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (depth - 1))) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int)))))) ” &&
  “ ((Znth ((depth - 1) - 1) cells __default__App_option_Z) = (Some ((Znth ((depth - 1) - 1) active (0 : Int))))) ”
  &&  (((( &( "stack" ) ) + (((depth - 1) - 1) * sizeof(INT)))) # Int |-> ((Znth ((depth - 1) - 1) active (0 : Int))))
  ** (intArray.mixed_missing_i ( &( "stack" ) ) ((depth - 1) - 1) (0 : Int) 1005 cells)
)

noncomputable def solver_entail_wit_5_1 : Prop :=
  (
forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (cells_2 : (List (Option Int))) (lengths_data_2 : (List Int)) (flat_data_2 : (List Int)) (total : Int) (active_2 : (List Int)) (depth : Int) (line : Int) (items_2 : (List (List Int))) (__default__App_option_Z : _App_option_Z) (PreH1 : ((Znth line last_numbers (0 : Int)) = 1)) (PreH2 : (line < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (n_pre = (Zlength (last_numbers)))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth (k_3) (last_numbers) ((0 : Int)))) ∧ ((Znth (k_3) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH7 : (Pre last_numbers)) (PreH8 : (Spec last_numbers items_2)) (PreH9 : ((Zlength (items_2)) = n_pre)) (PreH10 : ((0 : Int) <= line)) (PreH11 : (line <= n_pre)) (PreH12 : ((0 : Int) <= depth)) (PreH13 : (depth <= line)) (PreH14 : (depth = (Zlength (active_2)))) (PreH15 : (CurrentItem items_2 line active_2)) (PreH16 : (BoundedItem n_pre active_2)) (PreH17 : (total = (Zlength (flat_data_2)))) (PreH18 : ((0 : Int) <= total)) (PreH19 : (total <= (line * n_pre))) (PreH20 : (FlatPrefix items_2 line flat_data_2)) (PreH21 : (LengthsPrefix items_2 line lengths_data_2)) (PreH22 : ((Zlength (cells_2)) = 1005)) (PreH23 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < depth)) -> ((Znth k_4 cells_2 __default__App_option_Z) = (Some ((Znth k_4 active_2 (0 : Int))))))) ,
  (intArray.mixed_full ( &( "stack" ) ) 1005 (replace_Znth (depth) ((Some (1))) (cells_2)))
  ** (intArray.full values_pre n_pre last_numbers)
  ** ((( &( "x" ) )) # Int |-> ((Znth line last_numbers (0 : Int))))
  ** (intArray.seg flat_pre (0 : Int) total flat_data_2)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) line lengths_data_2)
  ** (intArray.undef_seg lengths_pre line n_pre)
|--
  EX cells : (List (Option Int)), EX lengths_data : (List Int), EX flat_data : (List Int), EX active : (List Int), EX items : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (n_pre = (Zlength (last_numbers))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre))) ” &&
  “ (Pre last_numbers) ” &&
  “ (Spec last_numbers items) ” &&
  “ ((Zlength (items)) = n_pre) ” &&
  “ ((0 : Int) <= line) ” &&
  “ (line < n_pre) ” &&
  “ (active = (Znth (line) (items) ((@List.nil Int)))) ” &&
  “ (1 <= (depth + 1)) ” &&
  “ ((depth + 1) <= (line + 1)) ” &&
  “ ((depth + 1) = (Zlength (active))) ” &&
  “ (BoundedItem n_pre active) ” &&
  “ (total = (Zlength (flat_data))) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= (line * n_pre)) ” &&
  “ (FlatPrefix items line flat_data) ” &&
  “ (LengthsPrefix items line lengths_data) ” &&
  “ ((Zlength (cells)) = 1005) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (depth + 1))) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int)))))) ”
  &&  ((( &( "x" ) )) # Int |->_)
  ** (intArray.full values_pre n_pre last_numbers)
  ** (intArray.mixed_full ( &( "stack" ) ) 1005 cells)
  ** (intArray.seg flat_pre (0 : Int) total flat_data)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) line lengths_data)
  ** (intArray.undef_seg lengths_pre line n_pre)
) \/
(
forall (n_pre : Int) (last_numbers : (List Int)) (cells_2 : (List (Option Int))) (lengths_data_2 : (List Int)) (flat_data_2 : (List Int)) (total : Int) (active_2 : (List Int)) (depth : Int) (line : Int) (items_2 : (List (List Int))) (__default__App_option_Z : _App_option_Z) (PreH1 : ((Znth line last_numbers (0 : Int)) = 1)) (PreH2 : (line < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (n_pre = (Zlength (last_numbers)))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth (k_3) (last_numbers) ((0 : Int)))) ∧ ((Znth (k_3) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH7 : (Pre last_numbers)) (PreH8 : (Spec last_numbers items_2)) (PreH9 : ((Zlength (items_2)) = n_pre)) (PreH10 : ((0 : Int) <= line)) (PreH11 : (line <= n_pre)) (PreH12 : ((0 : Int) <= depth)) (PreH13 : (depth <= line)) (PreH14 : (depth = (Zlength (active_2)))) (PreH15 : (CurrentItem items_2 line active_2)) (PreH16 : (BoundedItem n_pre active_2)) (PreH17 : (total = (Zlength (flat_data_2)))) (PreH18 : ((0 : Int) <= total)) (PreH19 : (total <= (line * n_pre))) (PreH20 : (FlatPrefix items_2 line flat_data_2)) (PreH21 : (LengthsPrefix items_2 line lengths_data_2)) (PreH22 : ((Zlength (cells_2)) = 1005)) (PreH23 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < depth)) -> ((Znth k_4 cells_2 __default__App_option_Z) = (Some ((Znth k_4 active_2 (0 : Int))))))) ,
  TT && emp 
|--
  EX items : (List (List Int)),
  “ (Spec last_numbers items) ” &&
  “ ((Zlength (items)) = (Zlength (last_numbers))) ” &&
  “ (1 <= ((Zlength (active_2)) + 1)) ” &&
  “ (((Zlength (active_2)) + 1) <= (line + 1)) ” &&
  “ (((Zlength (active_2)) + 1) = (Zlength ((Znth (line) (items) ((@List.nil Int)))))) ” &&
  “ (BoundedItem (Zlength (last_numbers)) (Znth (line) (items) ((@List.nil Int)))) ” &&
  “ (FlatPrefix items line flat_data_2) ” &&
  “ (LengthsPrefix items line lengths_data_2) ” &&
  “ ((Zlength ((replace_Znth ((Zlength (active_2))) ((Some (1))) (cells_2)))) = 1005) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < ((Zlength (active_2)) + 1))) -> ((Znth k_2 (replace_Znth ((Zlength (active_2))) ((Some (1))) (cells_2)) __default__App_option_Z) = (Some ((Znth k_2 (Znth (line) (items) ((@List.nil Int))) (0 : Int)))))) ”
  &&  emp
)

noncomputable def solver_entail_wit_5_2 : Prop :=
  (
forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (cells_2 : (List (Option Int))) (lengths_data_2 : (List Int)) (flat_data_2 : (List Int)) (total : Int) (active_2 : (List Int)) (depth : Int) (target : (List Int)) (x : Int) (line : Int) (items_2 : (List (List Int))) (__default__App_option_Z : _App_option_Z) (PreH1 : (((Znth (depth - 1) active_2 (0 : Int)) + 1) = x)) (PreH2 : (depth ≠ (0 : Int))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (n_pre = (Zlength (last_numbers)))) (PreH6 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth (k_3) (last_numbers) ((0 : Int)))) ∧ ((Znth (k_3) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH7 : (Pre last_numbers)) (PreH8 : (Spec last_numbers items_2)) (PreH9 : ((Zlength (items_2)) = n_pre)) (PreH10 : ((0 : Int) < line)) (PreH11 : (line < n_pre)) (PreH12 : (x = (Znth (line) (last_numbers) ((0 : Int))))) (PreH13 : (x ≠ 1)) (PreH14 : (target = (Znth (line) (items_2) ((@List.nil Int))))) (PreH15 : (1 <= depth)) (PreH16 : (depth <= line)) (PreH17 : (depth = (Zlength (active_2)))) (PreH18 : (PopTarget active_2 target x)) (PreH19 : (BoundedItem n_pre active_2)) (PreH20 : (total = (Zlength (flat_data_2)))) (PreH21 : ((0 : Int) <= total)) (PreH22 : (total <= (line * n_pre))) (PreH23 : (FlatPrefix items_2 line flat_data_2)) (PreH24 : (LengthsPrefix items_2 line lengths_data_2)) (PreH25 : ((Zlength (cells_2)) = 1005)) (PreH26 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < depth)) -> ((Znth k_4 cells_2 __default__App_option_Z) = (Some ((Znth k_4 active_2 (0 : Int))))))) (PreH27 : ((Znth (depth - 1) cells_2 __default__App_option_Z) = (Some ((Znth (depth - 1) active_2 (0 : Int)))))) ,
  ((( &( "x" ) )) # Int |-> (x))
  ** (intArray.full values_pre n_pre last_numbers)
  ** (((( &( "stack" ) ) + ((depth - 1) * sizeof(INT)))) # Int |-> (x))
  ** (intArray.mixed_missing_i ( &( "stack" ) ) (depth - 1) (0 : Int) 1005 cells_2)
  ** (intArray.seg flat_pre (0 : Int) total flat_data_2)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) line lengths_data_2)
  ** (intArray.undef_seg lengths_pre line n_pre)
|--
  EX cells : (List (Option Int)), EX lengths_data : (List Int), EX flat_data : (List Int), EX active : (List Int), EX items : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (n_pre = (Zlength (last_numbers))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre))) ” &&
  “ (Pre last_numbers) ” &&
  “ (Spec last_numbers items) ” &&
  “ ((Zlength (items)) = n_pre) ” &&
  “ ((0 : Int) <= line) ” &&
  “ (line < n_pre) ” &&
  “ (active = (Znth (line) (items) ((@List.nil Int)))) ” &&
  “ (1 <= depth) ” &&
  “ (depth <= (line + 1)) ” &&
  “ (depth = (Zlength (active))) ” &&
  “ (BoundedItem n_pre active) ” &&
  “ (total = (Zlength (flat_data))) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= (line * n_pre)) ” &&
  “ (FlatPrefix items line flat_data) ” &&
  “ (LengthsPrefix items line lengths_data) ” &&
  “ ((Zlength (cells)) = 1005) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int)))))) ”
  &&  ((( &( "x" ) )) # Int |->_)
  ** (intArray.full values_pre n_pre last_numbers)
  ** (intArray.mixed_full ( &( "stack" ) ) 1005 cells)
  ** (intArray.seg flat_pre (0 : Int) total flat_data)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) line lengths_data)
  ** (intArray.undef_seg lengths_pre line n_pre)
) \/
(
forall (n_pre : Int) (last_numbers : (List Int)) (cells_2 : (List (Option Int))) (lengths_data_2 : (List Int)) (flat_data_2 : (List Int)) (total : Int) (active_2 : (List Int)) (depth : Int) (target : (List Int)) (x : Int) (line : Int) (items_2 : (List (List Int))) (__default__App_option_Z : _App_option_Z) (PreH1 : (x <= INT_MAX)) (PreH2 : (x >= INT_MIN)) (PreH3 : (((Znth (depth - 1) active_2 (0 : Int)) + 1) = x)) (PreH4 : (depth ≠ (0 : Int))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (n_pre = (Zlength (last_numbers)))) (PreH8 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth (k_3) (last_numbers) ((0 : Int)))) ∧ ((Znth (k_3) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH9 : (Pre last_numbers)) (PreH10 : (Spec last_numbers items_2)) (PreH11 : ((Zlength (items_2)) = n_pre)) (PreH12 : ((0 : Int) < line)) (PreH13 : (line < n_pre)) (PreH14 : (x = (Znth (line) (last_numbers) ((0 : Int))))) (PreH15 : (x ≠ 1)) (PreH16 : (target = (Znth (line) (items_2) ((@List.nil Int))))) (PreH17 : (1 <= depth)) (PreH18 : (depth <= line)) (PreH19 : (depth = (Zlength (active_2)))) (PreH20 : (PopTarget active_2 target x)) (PreH21 : (BoundedItem n_pre active_2)) (PreH22 : (total = (Zlength (flat_data_2)))) (PreH23 : ((0 : Int) <= total)) (PreH24 : (total <= (line * n_pre))) (PreH25 : (FlatPrefix items_2 line flat_data_2)) (PreH26 : (LengthsPrefix items_2 line lengths_data_2)) (PreH27 : ((Zlength (cells_2)) = 1005)) (PreH28 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < depth)) -> ((Znth k_4 cells_2 __default__App_option_Z) = (Some ((Znth k_4 active_2 (0 : Int))))))) (PreH29 : ((Znth (depth - 1) cells_2 __default__App_option_Z) = (Some ((Znth (depth - 1) active_2 (0 : Int)))))) ,
  (((( &( "stack" ) ) + ((depth - 1) * sizeof(INT)))) # Int |-> (x))
  ** (intArray.mixed_missing_i ( &( "stack" ) ) (depth - 1) (0 : Int) 1005 cells_2)
|--
  EX cells : (List (Option Int)), EX items : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (n_pre = (Zlength (last_numbers))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre))) ” &&
  “ (Pre last_numbers) ” &&
  “ (Spec last_numbers items) ” &&
  “ ((Zlength (items)) = n_pre) ” &&
  “ ((0 : Int) <= line) ” &&
  “ (line < n_pre) ” &&
  “ (1 <= depth) ” &&
  “ (depth <= (line + 1)) ” &&
  “ (depth = (Zlength ((Znth (line) (items) ((@List.nil Int)))))) ” &&
  “ (BoundedItem n_pre (Znth (line) (items) ((@List.nil Int)))) ” &&
  “ (total = (Zlength (flat_data_2))) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= (line * n_pre)) ” &&
  “ (FlatPrefix items line flat_data_2) ” &&
  “ (LengthsPrefix items line lengths_data_2) ” &&
  “ ((Zlength (cells)) = 1005) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 (Znth (line) (items) ((@List.nil Int))) (0 : Int)))))) ”
  &&  (intArray.mixed_full ( &( "stack" ) ) 1005 cells)
)

noncomputable def solver_entail_wit_6 : Prop :=
  (
forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (items_2 : (List (List Int))) (cells_2 : (List (Option Int))) (active_2 : (List Int)) (flat_data_2 : (List Int)) (lengths_data_2 : (List Int)) (line : Int) (depth : Int) (total : Int) (__default__App_option_Z : _App_option_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (n_pre = (Zlength (last_numbers)))) (PreH4 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth (k_3) (last_numbers) ((0 : Int)))) ∧ ((Znth (k_3) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH5 : (Pre last_numbers)) (PreH6 : (Spec last_numbers items_2)) (PreH7 : ((Zlength (items_2)) = n_pre)) (PreH8 : ((0 : Int) <= line)) (PreH9 : (line < n_pre)) (PreH10 : (active_2 = (Znth (line) (items_2) ((@List.nil Int))))) (PreH11 : (1 <= depth)) (PreH12 : (depth <= (line + 1))) (PreH13 : (depth = (Zlength (active_2)))) (PreH14 : (BoundedItem n_pre active_2)) (PreH15 : (total = (Zlength (flat_data_2)))) (PreH16 : ((0 : Int) <= total)) (PreH17 : (total <= (line * n_pre))) (PreH18 : (FlatPrefix items_2 line flat_data_2)) (PreH19 : (LengthsPrefix items_2 line lengths_data_2)) (PreH20 : ((Zlength (cells_2)) = 1005)) (PreH21 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < depth)) -> ((Znth k_4 cells_2 __default__App_option_Z) = (Some ((Znth k_4 active_2 (0 : Int))))))) ,
  (intArray.seg lengths_pre (0 : Int) (line + 1) (lengths_data_2 ++ (depth :: (@List.nil Int))))
  ** (intArray.undef_seg lengths_pre (line + 1) n_pre)
  ** (intArray.full values_pre n_pre last_numbers)
  ** (intArray.mixed_full ( &( "stack" ) ) 1005 cells_2)
  ** (intArray.seg flat_pre (0 : Int) total flat_data_2)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
|--
  EX cells : (List (Option Int)), EX lengths_data : (List Int), EX flat_data : (List Int), EX flat_before : (List Int), EX active : (List Int), EX items : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (n_pre = (Zlength (last_numbers))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre))) ” &&
  “ (Pre last_numbers) ” &&
  “ (Spec last_numbers items) ” &&
  “ ((Zlength (items)) = n_pre) ” &&
  “ ((0 : Int) <= line) ” &&
  “ (line < n_pre) ” &&
  “ (active = (Znth (line) (items) ((@List.nil Int)))) ” &&
  “ (1 <= depth) ” &&
  “ (depth <= (line + 1)) ” &&
  “ ((line + 1) <= n_pre) ” &&
  “ (depth = (Zlength (active))) ” &&
  “ (BoundedItem n_pre active) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= depth) ” &&
  “ (FlatPrefix items line flat_before) ” &&
  “ (flat_data = (flat_before ++ (sublist ((0 : Int)) ((0 : Int)) (active)))) ” &&
  “ (total = (Zlength (flat_data))) ” &&
  “ ((0 : Int) <= total) ” &&
  “ ((total + (depth - (0 : Int))) <= ((line + 1) * n_pre)) ” &&
  “ (((line + 1) * n_pre) <= (n_pre * n_pre)) ” &&
  “ (LengthsPrefix items (line + 1) lengths_data) ” &&
  “ ((Zlength (cells)) = 1005) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int)))))) ”
  &&  (intArray.full values_pre n_pre last_numbers)
  ** (intArray.mixed_full ( &( "stack" ) ) 1005 cells)
  ** (intArray.seg flat_pre (0 : Int) total flat_data)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) (line + 1) lengths_data)
  ** (intArray.undef_seg lengths_pre (line + 1) n_pre)
) \/
(
forall (n_pre : Int) (last_numbers : (List Int)) (items_2 : (List (List Int))) (cells_2 : (List (Option Int))) (active_2 : (List Int)) (flat_data_2 : (List Int)) (lengths_data_2 : (List Int)) (line : Int) (depth : Int) (total : Int) (__default__App_option_Z : _App_option_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (n_pre = (Zlength (last_numbers)))) (PreH4 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth (k_3) (last_numbers) ((0 : Int)))) ∧ ((Znth (k_3) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH5 : (Pre last_numbers)) (PreH6 : (Spec last_numbers items_2)) (PreH7 : ((Zlength (items_2)) = n_pre)) (PreH8 : ((0 : Int) <= line)) (PreH9 : (line < n_pre)) (PreH10 : (active_2 = (Znth (line) (items_2) ((@List.nil Int))))) (PreH11 : (1 <= depth)) (PreH12 : (depth <= (line + 1))) (PreH13 : (depth = (Zlength (active_2)))) (PreH14 : (BoundedItem n_pre active_2)) (PreH15 : (total = (Zlength (flat_data_2)))) (PreH16 : ((0 : Int) <= total)) (PreH17 : (total <= (line * n_pre))) (PreH18 : (FlatPrefix items_2 line flat_data_2)) (PreH19 : (LengthsPrefix items_2 line lengths_data_2)) (PreH20 : ((Zlength (cells_2)) = 1005)) (PreH21 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < depth)) -> ((Znth k_4 cells_2 __default__App_option_Z) = (Some ((Znth k_4 active_2 (0 : Int))))))) ,
  TT && emp 
|--
  EX flat_before : (List Int), EX items : (List (List Int)),
  “ (flat_data_2 = (flat_before ++ (sublist ((0 : Int)) ((0 : Int)) ((Znth (line) (items) ((@List.nil Int))))))) ” &&
  “ (Spec last_numbers items) ” &&
  “ ((Zlength (items)) = (Zlength (last_numbers))) ” &&
  “ ((line + 1) <= (Zlength (last_numbers))) ” &&
  “ ((Zlength (active_2)) = (Zlength ((Znth (line) (items) ((@List.nil Int)))))) ” &&
  “ (BoundedItem (Zlength (last_numbers)) (Znth (line) (items) ((@List.nil Int)))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (Zlength (active_2))) ” &&
  “ (FlatPrefix items line flat_before) ” &&
  “ ((Zlength (flat_data_2)) = (Zlength ((flat_before ++ (sublist ((0 : Int)) ((0 : Int)) ((Znth (line) (items) ((@List.nil Int))))))))) ” &&
  “ (((Zlength (flat_data_2)) + ((Zlength (active_2)) - (0 : Int))) <= ((line + 1) * (Zlength (last_numbers)))) ” &&
  “ (((line + 1) * (Zlength (last_numbers))) <= ((Zlength (last_numbers)) * (Zlength (last_numbers)))) ” &&
  “ (LengthsPrefix items (line + 1) (lengths_data_2 ++ ((Zlength (active_2)) :: (@List.nil Int)))) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (active_2)))) -> ((Znth k_2 cells_2 __default__App_option_Z) = (Some ((Znth k_2 (Znth (line) (items) ((@List.nil Int))) (0 : Int)))))) ”
  &&  emp
)

noncomputable def solver_entail_wit_7 : Prop :=
  (
forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (cells_2 : (List (Option Int))) (lengths_data_2 : (List Int)) (total : Int) (flat_data_2 : (List Int)) (flat_before_2 : (List Int)) (i : Int) (depth : Int) (active_2 : (List Int)) (line : Int) (items_2 : (List (List Int))) (__default__App_option_Z : _App_option_Z) (PreH1 : (i < depth)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (last_numbers)))) (PreH5 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth (k_3) (last_numbers) ((0 : Int)))) ∧ ((Znth (k_3) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH6 : (Pre last_numbers)) (PreH7 : (Spec last_numbers items_2)) (PreH8 : ((Zlength (items_2)) = n_pre)) (PreH9 : ((0 : Int) <= line)) (PreH10 : (line < n_pre)) (PreH11 : (active_2 = (Znth (line) (items_2) ((@List.nil Int))))) (PreH12 : (1 <= depth)) (PreH13 : (depth <= (line + 1))) (PreH14 : ((line + 1) <= n_pre)) (PreH15 : (depth = (Zlength (active_2)))) (PreH16 : (BoundedItem n_pre active_2)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i <= depth)) (PreH19 : (FlatPrefix items_2 line flat_before_2)) (PreH20 : (flat_data_2 = (flat_before_2 ++ (sublist ((0 : Int)) (i) (active_2))))) (PreH21 : (total = (Zlength (flat_data_2)))) (PreH22 : ((0 : Int) <= total)) (PreH23 : ((total + (depth - i)) <= ((line + 1) * n_pre))) (PreH24 : (((line + 1) * n_pre) <= (n_pre * n_pre))) (PreH25 : (LengthsPrefix items_2 (line + 1) lengths_data_2)) (PreH26 : ((Zlength (cells_2)) = 1005)) (PreH27 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < depth)) -> ((Znth k_4 cells_2 __default__App_option_Z) = (Some ((Znth k_4 active_2 (0 : Int))))))) ,
  (intArray.full values_pre n_pre last_numbers)
  ** (intArray.mixed_full ( &( "stack" ) ) 1005 cells_2)
  ** (intArray.seg flat_pre (0 : Int) total flat_data_2)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) (line + 1) lengths_data_2)
  ** (intArray.undef_seg lengths_pre (line + 1) n_pre)
|--
  EX cells : (List (Option Int)), EX lengths_data : (List Int), EX flat_data : (List Int), EX flat_before : (List Int), EX active : (List Int), EX items : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (n_pre = (Zlength (last_numbers))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre))) ” &&
  “ (Pre last_numbers) ” &&
  “ (Spec last_numbers items) ” &&
  “ ((Zlength (items)) = n_pre) ” &&
  “ ((0 : Int) <= line) ” &&
  “ (line < n_pre) ” &&
  “ (active = (Znth (line) (items) ((@List.nil Int)))) ” &&
  “ (1 <= depth) ” &&
  “ (depth <= (line + 1)) ” &&
  “ ((line + 1) <= n_pre) ” &&
  “ (depth = (Zlength (active))) ” &&
  “ (BoundedItem n_pre active) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < depth) ” &&
  “ (FlatPrefix items line flat_before) ” &&
  “ (flat_data = (flat_before ++ (sublist ((0 : Int)) (i) (active)))) ” &&
  “ (total = (Zlength (flat_data))) ” &&
  “ ((0 : Int) <= total) ” &&
  “ ((total + (depth - i)) <= ((line + 1) * n_pre)) ” &&
  “ (((line + 1) * n_pre) <= (n_pre * n_pre)) ” &&
  “ (LengthsPrefix items (line + 1) lengths_data) ” &&
  “ ((Zlength (cells)) = 1005) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int)))))) ” &&
  “ ((Znth i cells __default__App_option_Z) = (Some ((Znth i active (0 : Int))))) ”
  &&  (intArray.full values_pre n_pre last_numbers)
  ** (((( &( "stack" ) ) + (i * sizeof(INT)))) # Int |-> ((Znth i active (0 : Int))))
  ** (intArray.mixed_missing_i ( &( "stack" ) ) i (0 : Int) 1005 cells)
  ** (intArray.seg flat_pre (0 : Int) total flat_data)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) (line + 1) lengths_data)
  ** (intArray.undef_seg lengths_pre (line + 1) n_pre)
) \/
(
forall (n_pre : Int) (last_numbers : (List Int)) (cells_2 : (List (Option Int))) (lengths_data_2 : (List Int)) (total : Int) (flat_data_2 : (List Int)) (flat_before_2 : (List Int)) (i : Int) (depth : Int) (active_2 : (List Int)) (line : Int) (items_2 : (List (List Int))) (__default__App_option_Z : _App_option_Z) (PreH1 : (i < depth)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (last_numbers)))) (PreH5 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth (k_3) (last_numbers) ((0 : Int)))) ∧ ((Znth (k_3) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH6 : (Pre last_numbers)) (PreH7 : (Spec last_numbers items_2)) (PreH8 : ((Zlength (items_2)) = n_pre)) (PreH9 : ((0 : Int) <= line)) (PreH10 : (line < n_pre)) (PreH11 : (active_2 = (Znth (line) (items_2) ((@List.nil Int))))) (PreH12 : (1 <= depth)) (PreH13 : (depth <= (line + 1))) (PreH14 : ((line + 1) <= n_pre)) (PreH15 : (depth = (Zlength (active_2)))) (PreH16 : (BoundedItem n_pre active_2)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i <= depth)) (PreH19 : (FlatPrefix items_2 line flat_before_2)) (PreH20 : (flat_data_2 = (flat_before_2 ++ (sublist ((0 : Int)) (i) (active_2))))) (PreH21 : (total = (Zlength (flat_data_2)))) (PreH22 : ((0 : Int) <= total)) (PreH23 : ((total + (depth - i)) <= ((line + 1) * n_pre))) (PreH24 : (((line + 1) * n_pre) <= (n_pre * n_pre))) (PreH25 : (LengthsPrefix items_2 (line + 1) lengths_data_2)) (PreH26 : ((Zlength (cells_2)) = 1005)) (PreH27 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < depth)) -> ((Znth k_4 cells_2 __default__App_option_Z) = (Some ((Znth k_4 active_2 (0 : Int))))))) ,
  TT && emp 
|--
  EX flat_before : (List Int), EX items : (List (List Int)),
  “ ((Znth i cells_2 __default__App_option_Z) = (Some ((Znth i (Znth (line) (items) ((@List.nil Int))) (0 : Int))))) ” &&
  “ ((flat_before_2 ++ (sublist ((0 : Int)) (i) (active_2))) = (flat_before ++ (sublist ((0 : Int)) (i) ((Znth (line) (items) ((@List.nil Int))))))) ” &&
  “ (Spec last_numbers items) ” &&
  “ ((Zlength (items)) = (Zlength (last_numbers))) ” &&
  “ ((Zlength (active_2)) = (Zlength ((Znth (line) (items) ((@List.nil Int)))))) ” &&
  “ (BoundedItem (Zlength (last_numbers)) (Znth (line) (items) ((@List.nil Int)))) ” &&
  “ (FlatPrefix items line flat_before) ” &&
  “ ((Zlength (flat_data_2)) = (Zlength ((flat_before ++ (sublist ((0 : Int)) (i) ((Znth (line) (items) ((@List.nil Int))))))))) ” &&
  “ (LengthsPrefix items (line + 1) lengths_data_2) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (active_2)))) -> ((Znth k_2 cells_2 __default__App_option_Z) = (Some ((Znth k_2 (Znth (line) (items) ((@List.nil Int))) (0 : Int)))))) ” &&
  “ ((Znth i cells_2 __default__App_option_Z) = (Some ((Znth i (Znth (line) (items) ((@List.nil Int))) (0 : Int))))) ”
  &&  emp
)

noncomputable def solver_entail_wit_8 : Prop :=
  (
forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (items_2 : (List (List Int))) (cells_2 : (List (Option Int))) (active_2 : (List Int)) (flat_before_2 : (List Int)) (flat_data_2 : (List Int)) (lengths_data_2 : (List Int)) (line : Int) (depth : Int) (i : Int) (total : Int) (__default__App_option_Z : _App_option_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (n_pre = (Zlength (last_numbers)))) (PreH4 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth (k_3) (last_numbers) ((0 : Int)))) ∧ ((Znth (k_3) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH5 : (Pre last_numbers)) (PreH6 : (Spec last_numbers items_2)) (PreH7 : ((Zlength (items_2)) = n_pre)) (PreH8 : ((0 : Int) <= line)) (PreH9 : (line < n_pre)) (PreH10 : (active_2 = (Znth (line) (items_2) ((@List.nil Int))))) (PreH11 : (1 <= depth)) (PreH12 : (depth <= (line + 1))) (PreH13 : ((line + 1) <= n_pre)) (PreH14 : (depth = (Zlength (active_2)))) (PreH15 : (BoundedItem n_pre active_2)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < depth)) (PreH18 : (FlatPrefix items_2 line flat_before_2)) (PreH19 : (flat_data_2 = (flat_before_2 ++ (sublist ((0 : Int)) (i) (active_2))))) (PreH20 : (total = (Zlength (flat_data_2)))) (PreH21 : ((0 : Int) <= total)) (PreH22 : ((total + (depth - i)) <= ((line + 1) * n_pre))) (PreH23 : (((line + 1) * n_pre) <= (n_pre * n_pre))) (PreH24 : (LengthsPrefix items_2 (line + 1) lengths_data_2)) (PreH25 : ((Zlength (cells_2)) = 1005)) (PreH26 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < depth)) -> ((Znth k_4 cells_2 __default__App_option_Z) = (Some ((Znth k_4 active_2 (0 : Int))))))) (PreH27 : ((Znth i cells_2 __default__App_option_Z) = (Some ((Znth i active_2 (0 : Int)))))) ,
  (intArray.seg flat_pre (0 : Int) (total + 1) (flat_data_2 ++ ((Znth i active_2 (0 : Int)) :: (@List.nil Int))))
  ** (intArray.mixed_full ( &( "stack" ) ) 1005 cells_2)
  ** (intArray.undef_seg flat_pre (total + 1) (n_pre * n_pre))
  ** (intArray.full values_pre n_pre last_numbers)
  ** (intArray.seg lengths_pre (0 : Int) (line + 1) lengths_data_2)
  ** (intArray.undef_seg lengths_pre (line + 1) n_pre)
|--
  EX cells : (List (Option Int)), EX lengths_data : (List Int), EX flat_data : (List Int), EX flat_before : (List Int), EX active : (List Int), EX items : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (n_pre = (Zlength (last_numbers))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre))) ” &&
  “ (Pre last_numbers) ” &&
  “ (Spec last_numbers items) ” &&
  “ ((Zlength (items)) = n_pre) ” &&
  “ ((0 : Int) <= line) ” &&
  “ (line < n_pre) ” &&
  “ (active = (Znth (line) (items) ((@List.nil Int)))) ” &&
  “ (1 <= depth) ” &&
  “ (depth <= (line + 1)) ” &&
  “ ((line + 1) <= n_pre) ” &&
  “ (depth = (Zlength (active))) ” &&
  “ (BoundedItem n_pre active) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= depth) ” &&
  “ (FlatPrefix items line flat_before) ” &&
  “ (flat_data = (flat_before ++ (sublist ((0 : Int)) ((i + 1)) (active)))) ” &&
  “ ((total + 1) = (Zlength (flat_data))) ” &&
  “ ((0 : Int) <= (total + 1)) ” &&
  “ (((total + 1) + (depth - (i + 1))) <= ((line + 1) * n_pre)) ” &&
  “ (((line + 1) * n_pre) <= (n_pre * n_pre)) ” &&
  “ (LengthsPrefix items (line + 1) lengths_data) ” &&
  “ ((Zlength (cells)) = 1005) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int)))))) ”
  &&  (intArray.full values_pre n_pre last_numbers)
  ** (intArray.mixed_full ( &( "stack" ) ) 1005 cells)
  ** (intArray.seg flat_pre (0 : Int) (total + 1) flat_data)
  ** (intArray.undef_seg flat_pre (total + 1) (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) (line + 1) lengths_data)
  ** (intArray.undef_seg lengths_pre (line + 1) n_pre)
) \/
(
forall (n_pre : Int) (last_numbers : (List Int)) (items_2 : (List (List Int))) (cells_2 : (List (Option Int))) (active_2 : (List Int)) (flat_before_2 : (List Int)) (flat_data_2 : (List Int)) (lengths_data_2 : (List Int)) (line : Int) (depth : Int) (i : Int) (total : Int) (__default__App_option_Z : _App_option_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (n_pre = (Zlength (last_numbers)))) (PreH4 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth (k_3) (last_numbers) ((0 : Int)))) ∧ ((Znth (k_3) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH5 : (Pre last_numbers)) (PreH6 : (Spec last_numbers items_2)) (PreH7 : ((Zlength (items_2)) = n_pre)) (PreH8 : ((0 : Int) <= line)) (PreH9 : (line < n_pre)) (PreH10 : (active_2 = (Znth (line) (items_2) ((@List.nil Int))))) (PreH11 : (1 <= depth)) (PreH12 : (depth <= (line + 1))) (PreH13 : ((line + 1) <= n_pre)) (PreH14 : (depth = (Zlength (active_2)))) (PreH15 : (BoundedItem n_pre active_2)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < depth)) (PreH18 : (FlatPrefix items_2 line flat_before_2)) (PreH19 : (flat_data_2 = (flat_before_2 ++ (sublist ((0 : Int)) (i) (active_2))))) (PreH20 : (total = (Zlength (flat_data_2)))) (PreH21 : ((0 : Int) <= total)) (PreH22 : ((total + (depth - i)) <= ((line + 1) * n_pre))) (PreH23 : (((line + 1) * n_pre) <= (n_pre * n_pre))) (PreH24 : (LengthsPrefix items_2 (line + 1) lengths_data_2)) (PreH25 : ((Zlength (cells_2)) = 1005)) (PreH26 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < depth)) -> ((Znth k_4 cells_2 __default__App_option_Z) = (Some ((Znth k_4 active_2 (0 : Int))))))) (PreH27 : ((Znth i cells_2 __default__App_option_Z) = (Some ((Znth i active_2 (0 : Int)))))) ,
  TT && emp 
|--
  EX flat_before : (List Int), EX items : (List (List Int)),
  “ (((flat_before_2 ++ (sublist ((0 : Int)) (i) (active_2))) ++ ((Znth i (Znth (line) (items_2) ((@List.nil Int))) (0 : Int)) :: (@List.nil Int))) = (flat_before ++ (sublist ((0 : Int)) ((i + 1)) ((Znth (line) (items) ((@List.nil Int))))))) ” &&
  “ (Spec last_numbers items) ” &&
  “ ((Zlength (items)) = (Zlength (last_numbers))) ” &&
  “ ((Zlength (active_2)) = (Zlength ((Znth (line) (items) ((@List.nil Int)))))) ” &&
  “ (BoundedItem (Zlength (last_numbers)) (Znth (line) (items) ((@List.nil Int)))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (Zlength (active_2))) ” &&
  “ (FlatPrefix items line flat_before) ” &&
  “ (((Zlength (flat_data_2)) + 1) = (Zlength ((flat_before ++ (sublist ((0 : Int)) ((i + 1)) ((Znth (line) (items) ((@List.nil Int))))))))) ” &&
  “ ((0 : Int) <= ((Zlength (flat_data_2)) + 1)) ” &&
  “ ((((Zlength (flat_data_2)) + 1) + ((Zlength (active_2)) - (i + 1))) <= ((line + 1) * (Zlength (last_numbers)))) ” &&
  “ (LengthsPrefix items (line + 1) lengths_data_2) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (active_2)))) -> ((Znth k_2 cells_2 __default__App_option_Z) = (Some ((Znth k_2 (Znth (line) (items) ((@List.nil Int))) (0 : Int)))))) ”
  &&  emp
)

noncomputable def solver_entail_wit_9 : Prop :=
  (
forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (cells_2 : (List (Option Int))) (lengths_data_2 : (List Int)) (total : Int) (flat_data_2 : (List Int)) (flat_before : (List Int)) (i : Int) (depth : Int) (active_2 : (List Int)) (line : Int) (items_2 : (List (List Int))) (__default__App_option_Z : _App_option_Z) (PreH1 : (i >= depth)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (last_numbers)))) (PreH5 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth (k_3) (last_numbers) ((0 : Int)))) ∧ ((Znth (k_3) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH6 : (Pre last_numbers)) (PreH7 : (Spec last_numbers items_2)) (PreH8 : ((Zlength (items_2)) = n_pre)) (PreH9 : ((0 : Int) <= line)) (PreH10 : (line < n_pre)) (PreH11 : (active_2 = (Znth (line) (items_2) ((@List.nil Int))))) (PreH12 : (1 <= depth)) (PreH13 : (depth <= (line + 1))) (PreH14 : ((line + 1) <= n_pre)) (PreH15 : (depth = (Zlength (active_2)))) (PreH16 : (BoundedItem n_pre active_2)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i <= depth)) (PreH19 : (FlatPrefix items_2 line flat_before)) (PreH20 : (flat_data_2 = (flat_before ++ (sublist ((0 : Int)) (i) (active_2))))) (PreH21 : (total = (Zlength (flat_data_2)))) (PreH22 : ((0 : Int) <= total)) (PreH23 : ((total + (depth - i)) <= ((line + 1) * n_pre))) (PreH24 : (((line + 1) * n_pre) <= (n_pre * n_pre))) (PreH25 : (LengthsPrefix items_2 (line + 1) lengths_data_2)) (PreH26 : ((Zlength (cells_2)) = 1005)) (PreH27 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < depth)) -> ((Znth k_4 cells_2 __default__App_option_Z) = (Some ((Znth k_4 active_2 (0 : Int))))))) ,
  (intArray.full values_pre n_pre last_numbers)
  ** (intArray.mixed_full ( &( "stack" ) ) 1005 cells_2)
  ** (intArray.seg flat_pre (0 : Int) total flat_data_2)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) (line + 1) lengths_data_2)
  ** (intArray.undef_seg lengths_pre (line + 1) n_pre)
|--
  EX cells : (List (Option Int)), EX lengths_data : (List Int), EX flat_data : (List Int), EX active : (List Int), EX items : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (n_pre = (Zlength (last_numbers))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre))) ” &&
  “ (Pre last_numbers) ” &&
  “ (Spec last_numbers items) ” &&
  “ ((Zlength (items)) = n_pre) ” &&
  “ ((0 : Int) <= (line + 1)) ” &&
  “ ((line + 1) <= n_pre) ” &&
  “ ((0 : Int) <= depth) ” &&
  “ (depth <= (line + 1)) ” &&
  “ (depth = (Zlength (active))) ” &&
  “ (CurrentItem items (line + 1) active) ” &&
  “ (BoundedItem n_pre active) ” &&
  “ (total = (Zlength (flat_data))) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= ((line + 1) * n_pre)) ” &&
  “ (FlatPrefix items (line + 1) flat_data) ” &&
  “ (LengthsPrefix items (line + 1) lengths_data) ” &&
  “ ((Zlength (cells)) = 1005) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int)))))) ”
  &&  (intArray.full values_pre n_pre last_numbers)
  ** (intArray.mixed_full ( &( "stack" ) ) 1005 cells)
  ** (intArray.seg flat_pre (0 : Int) total flat_data)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) (line + 1) lengths_data)
  ** (intArray.undef_seg lengths_pre (line + 1) n_pre)
) \/
(
forall (n_pre : Int) (last_numbers : (List Int)) (cells_2 : (List (Option Int))) (lengths_data_2 : (List Int)) (total : Int) (flat_data_2 : (List Int)) (flat_before : (List Int)) (i : Int) (depth : Int) (active_2 : (List Int)) (line : Int) (items_2 : (List (List Int))) (__default__App_option_Z : _App_option_Z) (PreH1 : (i >= depth)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (last_numbers)))) (PreH5 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < n_pre)) -> ((1 <= (Znth (k_3) (last_numbers) ((0 : Int)))) ∧ ((Znth (k_3) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH6 : (Pre last_numbers)) (PreH7 : (Spec last_numbers items_2)) (PreH8 : ((Zlength (items_2)) = n_pre)) (PreH9 : ((0 : Int) <= line)) (PreH10 : (line < n_pre)) (PreH11 : (active_2 = (Znth (line) (items_2) ((@List.nil Int))))) (PreH12 : (1 <= depth)) (PreH13 : (depth <= (line + 1))) (PreH14 : ((line + 1) <= n_pre)) (PreH15 : (depth = (Zlength (active_2)))) (PreH16 : (BoundedItem n_pre active_2)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i <= depth)) (PreH19 : (FlatPrefix items_2 line flat_before)) (PreH20 : (flat_data_2 = (flat_before ++ (sublist ((0 : Int)) (i) (active_2))))) (PreH21 : (total = (Zlength (flat_data_2)))) (PreH22 : ((0 : Int) <= total)) (PreH23 : ((total + (depth - i)) <= ((line + 1) * n_pre))) (PreH24 : (((line + 1) * n_pre) <= (n_pre * n_pre))) (PreH25 : (LengthsPrefix items_2 (line + 1) lengths_data_2)) (PreH26 : ((Zlength (cells_2)) = 1005)) (PreH27 : forall (k_4 : Int) , ((((0 : Int) <= k_4) ∧ (k_4 < depth)) -> ((Znth k_4 cells_2 __default__App_option_Z) = (Some ((Znth k_4 active_2 (0 : Int))))))) ,
  TT && emp 
|--
  EX active : (List Int), EX items : (List (List Int)),
  “ (Spec last_numbers items) ” &&
  “ ((Zlength (items)) = (Zlength (last_numbers))) ” &&
  “ ((0 : Int) <= (line + 1)) ” &&
  “ ((0 : Int) <= (Zlength (active_2))) ” &&
  “ ((Zlength (active_2)) = (Zlength (active))) ” &&
  “ (CurrentItem items (line + 1) active) ” &&
  “ (BoundedItem (Zlength (last_numbers)) active) ” &&
  “ ((Zlength (flat_data_2)) <= ((line + 1) * (Zlength (last_numbers)))) ” &&
  “ (FlatPrefix items (line + 1) (flat_before ++ (sublist ((0 : Int)) (i) (active_2)))) ” &&
  “ (LengthsPrefix items (line + 1) lengths_data_2) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < (Zlength (active_2)))) -> ((Znth k_2 cells_2 __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int)))))) ”
  &&  emp
)

noncomputable def solver_entail_wit_10 : Prop :=
  (
forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (cells : (List (Option Int))) (lengths_data_2 : (List Int)) (flat_data_2 : (List Int)) (total : Int) (active : (List Int)) (depth : Int) (line : Int) (items_2 : (List (List Int))) (__default__App_option_Z : _App_option_Z) (__default__List_Z : _List_Z) (PreH1 : (line >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (last_numbers)))) (PreH5 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((1 <= (Znth (k_2) (last_numbers) ((0 : Int)))) ∧ ((Znth (k_2) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH6 : (Pre last_numbers)) (PreH7 : (Spec last_numbers items_2)) (PreH8 : ((Zlength (items_2)) = n_pre)) (PreH9 : ((0 : Int) <= line)) (PreH10 : (line <= n_pre)) (PreH11 : ((0 : Int) <= depth)) (PreH12 : (depth <= line)) (PreH13 : (depth = (Zlength (active)))) (PreH14 : (CurrentItem items_2 line active)) (PreH15 : (BoundedItem n_pre active)) (PreH16 : (total = (Zlength (flat_data_2)))) (PreH17 : ((0 : Int) <= total)) (PreH18 : (total <= (line * n_pre))) (PreH19 : (FlatPrefix items_2 line flat_data_2)) (PreH20 : (LengthsPrefix items_2 line lengths_data_2)) (PreH21 : ((Zlength (cells)) = 1005)) (PreH22 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < depth)) -> ((Znth k_3 cells __default__App_option_Z) = (Some ((Znth k_3 active (0 : Int))))))) ,
  ((( &( "depth" ) )) # Int |-> (depth))
  ** (intArray.full values_pre n_pre last_numbers)
  ** (intArray.mixed_full ( &( "stack" ) ) 1005 cells)
  ** (intArray.seg flat_pre (0 : Int) total flat_data_2)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) line lengths_data_2)
  ** (intArray.undef_seg lengths_pre line n_pre)
|--
  EX lengths_data : (List Int), EX flat_data : (List Int), EX items : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (n_pre = (Zlength (last_numbers))) ” &&
  “ (Spec last_numbers items) ” &&
  “ ((Zlength (items)) = n_pre) ” &&
  “ (flat_data = (List.flatten (items))) ” &&
  “ (total = (Zlength (flat_data))) ” &&
  “ ((Zlength (lengths_data)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((Znth k lengths_data (0 : Int)) = (Zlength ((Znth k items __default__List_Z))))) ”
  &&  ((( &( "depth" ) )) # Int |->_)
  ** (intArray.full values_pre n_pre last_numbers)
  ** (intArray.undef_full ( &( "stack" ) ) 1005)
  ** (intArray.full flat_pre total flat_data)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.full lengths_pre n_pre lengths_data)
) \/
(
forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (last_numbers : (List Int)) (cells : (List (Option Int))) (lengths_data_2 : (List Int)) (flat_data_2 : (List Int)) (total : Int) (active : (List Int)) (depth : Int) (line : Int) (items_2 : (List (List Int))) (__default__App_option_Z : _App_option_Z) (__default__List_Z : _List_Z) (PreH1 : (line >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (last_numbers)))) (PreH5 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < n_pre)) -> ((1 <= (Znth (k_2) (last_numbers) ((0 : Int)))) ∧ ((Znth (k_2) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH6 : (Pre last_numbers)) (PreH7 : (Spec last_numbers items_2)) (PreH8 : ((Zlength (items_2)) = n_pre)) (PreH9 : ((0 : Int) <= line)) (PreH10 : (line <= n_pre)) (PreH11 : ((0 : Int) <= depth)) (PreH12 : (depth <= line)) (PreH13 : (depth = (Zlength (active)))) (PreH14 : (CurrentItem items_2 line active)) (PreH15 : (BoundedItem n_pre active)) (PreH16 : (total = (Zlength (flat_data_2)))) (PreH17 : ((0 : Int) <= total)) (PreH18 : (total <= (line * n_pre))) (PreH19 : (FlatPrefix items_2 line flat_data_2)) (PreH20 : (LengthsPrefix items_2 line lengths_data_2)) (PreH21 : ((Zlength (cells)) = 1005)) (PreH22 : forall (k_3 : Int) , ((((0 : Int) <= k_3) ∧ (k_3 < depth)) -> ((Znth k_3 cells __default__App_option_Z) = (Some ((Znth k_3 active (0 : Int))))))) ,
  (intArray.mixed_full ( &( "stack" ) ) 1005 cells)
  ** (intArray.seg flat_pre (0 : Int) total flat_data_2)
  ** (intArray.seg lengths_pre (0 : Int) line lengths_data_2)
|--
  EX lengths_data : (List Int), EX items : (List (List Int)),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (n_pre = (Zlength (last_numbers))) ” &&
  “ (Spec last_numbers items) ” &&
  “ ((Zlength (items)) = n_pre) ” &&
  “ (total = (Zlength ((List.flatten (items))))) ” &&
  “ ((Zlength (lengths_data)) = n_pre) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((Znth k lengths_data (0 : Int)) = (Zlength ((Znth k items __default__List_Z))))) ”
  &&  (intArray.undef_full ( &( "stack" ) ) 1005)
  ** (intArray.full flat_pre total (List.flatten (items)))
  ** (intArray.full lengths_pre n_pre lengths_data)
)

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (items : (List (List Int))) (flat_data : (List Int)) (lengths_data_2 : (List Int)) (total : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (n_pre = (Zlength (last_numbers)))) (PreH4 : (Spec last_numbers items)) (PreH5 : ((Zlength (items)) = n_pre)) (PreH6 : (flat_data = (List.flatten (items)))) (PreH7 : (total = (Zlength (flat_data)))) (PreH8 : ((Zlength (lengths_data_2)) = n_pre)) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((Znth k lengths_data_2 (0 : Int)) = (Zlength ((Znth k items __default__List_Z)))))) ,
  (intArray.full values_pre n_pre last_numbers)
  ** (intArray.full flat_pre total flat_data)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.full lengths_pre n_pre lengths_data_2)
|--
  EX lengths_data : (List Int), EX result : (List (List Int)),
  “ (Spec last_numbers result) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((Znth i lengths_data (0 : Int)) = (Zlength ((Znth i result __default__List_Z))))) ” &&
  “ (total = (Zlength ((List.flatten (result))))) ”
  &&  (intArray.full values_pre n_pre last_numbers)
  ** (intArray.full flat_pre (Zlength ((List.flatten (result)))) (List.flatten (result)))
  ** (intArray.undef_seg flat_pre (Zlength ((List.flatten (result)))) (n_pre * n_pre))
  ** (intArray.full lengths_pre n_pre lengths_data)
) \/
(
forall (flat_pre : Int) (n_pre : Int) (last_numbers : (List Int)) (items : (List (List Int))) (flat_data : (List Int)) (lengths_data_2 : (List Int)) (total : Int) (__default__List_Z : _List_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (n_pre = (Zlength (last_numbers)))) (PreH4 : (Spec last_numbers items)) (PreH5 : ((Zlength (items)) = n_pre)) (PreH6 : (flat_data = (List.flatten (items)))) (PreH7 : (total = (Zlength (flat_data)))) (PreH8 : ((Zlength (lengths_data_2)) = n_pre)) (PreH9 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((Znth k lengths_data_2 (0 : Int)) = (Zlength ((Znth k items __default__List_Z)))))) ,
  (intArray.full flat_pre total flat_data)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
|--
  EX result : (List (List Int)),
  “ (Spec last_numbers result) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((Znth i lengths_data_2 (0 : Int)) = (Zlength ((Znth i result __default__List_Z))))) ” &&
  “ (total = (Zlength ((List.flatten (result))))) ”
  &&  (intArray.full flat_pre (Zlength ((List.flatten (result)))) (List.flatten (result)))
  ** (intArray.undef_seg flat_pre (Zlength ((List.flatten (result)))) (n_pre * n_pre))
)

noncomputable def solver_partial_solve_wit_1 : Prop :=
  forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (cells : (List (Option Int))) (lengths_data : (List Int)) (flat_data : (List Int)) (total : Int) (active : (List Int)) (depth : Int) (line : Int) (items : (List (List Int))) (__default__App_option_Z : _App_option_Z) (PreH1 : (line < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (last_numbers)))) (PreH5 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH6 : (Pre last_numbers)) (PreH7 : (Spec last_numbers items)) (PreH8 : ((Zlength (items)) = n_pre)) (PreH9 : ((0 : Int) <= line)) (PreH10 : (line <= n_pre)) (PreH11 : ((0 : Int) <= depth)) (PreH12 : (depth <= line)) (PreH13 : (depth = (Zlength (active)))) (PreH14 : (CurrentItem items line active)) (PreH15 : (BoundedItem n_pre active)) (PreH16 : (total = (Zlength (flat_data)))) (PreH17 : ((0 : Int) <= total)) (PreH18 : (total <= (line * n_pre))) (PreH19 : (FlatPrefix items line flat_data)) (PreH20 : (LengthsPrefix items line lengths_data)) (PreH21 : ((Zlength (cells)) = 1005)) (PreH22 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int))))))) ,
  (intArray.full values_pre n_pre last_numbers)
  ** (intArray.mixed_full ( &( "stack" ) ) 1005 cells)
  ** (intArray.seg flat_pre (0 : Int) total flat_data)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) line lengths_data)
  ** (intArray.undef_seg lengths_pre line n_pre)
|--
  “ (line < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (n_pre = (Zlength (last_numbers))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre))) ” &&
  “ (Pre last_numbers) ” &&
  “ (Spec last_numbers items) ” &&
  “ ((Zlength (items)) = n_pre) ” &&
  “ ((0 : Int) <= line) ” &&
  “ (line <= n_pre) ” &&
  “ ((0 : Int) <= depth) ” &&
  “ (depth <= line) ” &&
  “ (depth = (Zlength (active))) ” &&
  “ (CurrentItem items line active) ” &&
  “ (BoundedItem n_pre active) ” &&
  “ (total = (Zlength (flat_data))) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= (line * n_pre)) ” &&
  “ (FlatPrefix items line flat_data) ” &&
  “ (LengthsPrefix items line lengths_data) ” &&
  “ ((Zlength (cells)) = 1005) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int)))))) ”
  &&  (((values_pre + (line * sizeof(INT)))) # Int |-> ((Znth line last_numbers (0 : Int))))
  ** (intArray.missing_i values_pre line (0 : Int) n_pre last_numbers)
  ** (intArray.mixed_full ( &( "stack" ) ) 1005 cells)
  ** (intArray.seg flat_pre (0 : Int) total flat_data)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) line lengths_data)
  ** (intArray.undef_seg lengths_pre line n_pre)

noncomputable def solver_partial_solve_wit_2 : Prop :=
  forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (cells : (List (Option Int))) (lengths_data : (List Int)) (flat_data : (List Int)) (total : Int) (active : (List Int)) (depth : Int) (line : Int) (items : (List (List Int))) (__default__App_option_Z : _App_option_Z) (PreH1 : ((Znth line last_numbers (0 : Int)) = 1)) (PreH2 : (line < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (n_pre = (Zlength (last_numbers)))) (PreH6 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH7 : (Pre last_numbers)) (PreH8 : (Spec last_numbers items)) (PreH9 : ((Zlength (items)) = n_pre)) (PreH10 : ((0 : Int) <= line)) (PreH11 : (line <= n_pre)) (PreH12 : ((0 : Int) <= depth)) (PreH13 : (depth <= line)) (PreH14 : (depth = (Zlength (active)))) (PreH15 : (CurrentItem items line active)) (PreH16 : (BoundedItem n_pre active)) (PreH17 : (total = (Zlength (flat_data)))) (PreH18 : ((0 : Int) <= total)) (PreH19 : (total <= (line * n_pre))) (PreH20 : (FlatPrefix items line flat_data)) (PreH21 : (LengthsPrefix items line lengths_data)) (PreH22 : ((Zlength (cells)) = 1005)) (PreH23 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int))))))) ,
  (intArray.full values_pre n_pre last_numbers)
  ** (intArray.mixed_full ( &( "stack" ) ) 1005 cells)
  ** (intArray.seg flat_pre (0 : Int) total flat_data)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) line lengths_data)
  ** (intArray.undef_seg lengths_pre line n_pre)
|--
  “ ((Znth line last_numbers (0 : Int)) = 1) ” &&
  “ (line < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (n_pre = (Zlength (last_numbers))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre))) ” &&
  “ (Pre last_numbers) ” &&
  “ (Spec last_numbers items) ” &&
  “ ((Zlength (items)) = n_pre) ” &&
  “ ((0 : Int) <= line) ” &&
  “ (line <= n_pre) ” &&
  “ ((0 : Int) <= depth) ” &&
  “ (depth <= line) ” &&
  “ (depth = (Zlength (active))) ” &&
  “ (CurrentItem items line active) ” &&
  “ (BoundedItem n_pre active) ” &&
  “ (total = (Zlength (flat_data))) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= (line * n_pre)) ” &&
  “ (FlatPrefix items line flat_data) ” &&
  “ (LengthsPrefix items line lengths_data) ” &&
  “ ((Zlength (cells)) = 1005) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int)))))) ”
  &&  (((( &( "stack" ) ) + (depth * sizeof(INT)))) # Int |->_)
  ** (intArray.mixed_missing_i ( &( "stack" ) ) depth (0 : Int) 1005 cells)
  ** (intArray.full values_pre n_pre last_numbers)
  ** (intArray.seg flat_pre (0 : Int) total flat_data)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) line lengths_data)
  ** (intArray.undef_seg lengths_pre line n_pre)

noncomputable def solver_partial_solve_wit_3 : Prop :=
  forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (items : (List (List Int))) (cells : (List (Option Int))) (active : (List Int)) (flat_data : (List Int)) (lengths_data : (List Int)) (line : Int) (depth : Int) (total : Int) (__default__App_option_Z : _App_option_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (n_pre = (Zlength (last_numbers)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH5 : (Pre last_numbers)) (PreH6 : (Spec last_numbers items)) (PreH7 : ((Zlength (items)) = n_pre)) (PreH8 : ((0 : Int) <= line)) (PreH9 : (line < n_pre)) (PreH10 : (active = (Znth (line) (items) ((@List.nil Int))))) (PreH11 : (1 <= depth)) (PreH12 : (depth <= (line + 1))) (PreH13 : (depth = (Zlength (active)))) (PreH14 : (BoundedItem n_pre active)) (PreH15 : (total = (Zlength (flat_data)))) (PreH16 : ((0 : Int) <= total)) (PreH17 : (total <= (line * n_pre))) (PreH18 : (FlatPrefix items line flat_data)) (PreH19 : (LengthsPrefix items line lengths_data)) (PreH20 : ((Zlength (cells)) = 1005)) (PreH21 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int))))))) ,
  (intArray.full values_pre n_pre last_numbers)
  ** (intArray.mixed_full ( &( "stack" ) ) 1005 cells)
  ** (intArray.seg flat_pre (0 : Int) total flat_data)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) line lengths_data)
  ** (intArray.undef_seg lengths_pre line n_pre)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (n_pre = (Zlength (last_numbers))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre))) ” &&
  “ (Pre last_numbers) ” &&
  “ (Spec last_numbers items) ” &&
  “ ((Zlength (items)) = n_pre) ” &&
  “ ((0 : Int) <= line) ” &&
  “ (line < n_pre) ” &&
  “ (active = (Znth (line) (items) ((@List.nil Int)))) ” &&
  “ (1 <= depth) ” &&
  “ (depth <= (line + 1)) ” &&
  “ (depth = (Zlength (active))) ” &&
  “ (BoundedItem n_pre active) ” &&
  “ (total = (Zlength (flat_data))) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= (line * n_pre)) ” &&
  “ (FlatPrefix items line flat_data) ” &&
  “ (LengthsPrefix items line lengths_data) ” &&
  “ ((Zlength (cells)) = 1005) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int)))))) ”
  &&  (((lengths_pre + (line * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg lengths_pre (line + 1) n_pre)
  ** (intArray.full values_pre n_pre last_numbers)
  ** (intArray.mixed_full ( &( "stack" ) ) 1005 cells)
  ** (intArray.seg flat_pre (0 : Int) total flat_data)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) line lengths_data)

noncomputable def solver_partial_solve_wit_4 : Prop :=
  forall (lengths_pre : Int) (flat_pre : Int) (n_pre : Int) (values_pre : Int) (last_numbers : (List Int)) (items : (List (List Int))) (cells : (List (Option Int))) (active : (List Int)) (flat_before : (List Int)) (flat_data : (List Int)) (lengths_data : (List Int)) (line : Int) (depth : Int) (i : Int) (total : Int) (__default__App_option_Z : _App_option_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (n_pre = (Zlength (last_numbers)))) (PreH4 : forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre)))) (PreH5 : (Pre last_numbers)) (PreH6 : (Spec last_numbers items)) (PreH7 : ((Zlength (items)) = n_pre)) (PreH8 : ((0 : Int) <= line)) (PreH9 : (line < n_pre)) (PreH10 : (active = (Znth (line) (items) ((@List.nil Int))))) (PreH11 : (1 <= depth)) (PreH12 : (depth <= (line + 1))) (PreH13 : ((line + 1) <= n_pre)) (PreH14 : (depth = (Zlength (active)))) (PreH15 : (BoundedItem n_pre active)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < depth)) (PreH18 : (FlatPrefix items line flat_before)) (PreH19 : (flat_data = (flat_before ++ (sublist ((0 : Int)) (i) (active))))) (PreH20 : (total = (Zlength (flat_data)))) (PreH21 : ((0 : Int) <= total)) (PreH22 : ((total + (depth - i)) <= ((line + 1) * n_pre))) (PreH23 : (((line + 1) * n_pre) <= (n_pre * n_pre))) (PreH24 : (LengthsPrefix items (line + 1) lengths_data)) (PreH25 : ((Zlength (cells)) = 1005)) (PreH26 : forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int))))))) (PreH27 : ((Znth i cells __default__App_option_Z) = (Some ((Znth i active (0 : Int)))))) ,
  (intArray.full values_pre n_pre last_numbers)
  ** (((( &( "stack" ) ) + (i * sizeof(INT)))) # Int |-> ((Znth i active (0 : Int))))
  ** (intArray.mixed_missing_i ( &( "stack" ) ) i (0 : Int) 1005 cells)
  ** (intArray.seg flat_pre (0 : Int) total flat_data)
  ** (intArray.undef_seg flat_pre total (n_pre * n_pre))
  ** (intArray.seg lengths_pre (0 : Int) (line + 1) lengths_data)
  ** (intArray.undef_seg lengths_pre (line + 1) n_pre)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ (n_pre = (Zlength (last_numbers))) ” &&
  “ forall (k : Int) , ((((0 : Int) <= k) ∧ (k < n_pre)) -> ((1 <= (Znth (k) (last_numbers) ((0 : Int)))) ∧ ((Znth (k) (last_numbers) ((0 : Int))) <= n_pre))) ” &&
  “ (Pre last_numbers) ” &&
  “ (Spec last_numbers items) ” &&
  “ ((Zlength (items)) = n_pre) ” &&
  “ ((0 : Int) <= line) ” &&
  “ (line < n_pre) ” &&
  “ (active = (Znth (line) (items) ((@List.nil Int)))) ” &&
  “ (1 <= depth) ” &&
  “ (depth <= (line + 1)) ” &&
  “ ((line + 1) <= n_pre) ” &&
  “ (depth = (Zlength (active))) ” &&
  “ (BoundedItem n_pre active) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < depth) ” &&
  “ (FlatPrefix items line flat_before) ” &&
  “ (flat_data = (flat_before ++ (sublist ((0 : Int)) (i) (active)))) ” &&
  “ (total = (Zlength (flat_data))) ” &&
  “ ((0 : Int) <= total) ” &&
  “ ((total + (depth - i)) <= ((line + 1) * n_pre)) ” &&
  “ (((line + 1) * n_pre) <= (n_pre * n_pre)) ” &&
  “ (LengthsPrefix items (line + 1) lengths_data) ” &&
  “ ((Zlength (cells)) = 1005) ” &&
  “ forall (k_2 : Int) , ((((0 : Int) <= k_2) ∧ (k_2 < depth)) -> ((Znth k_2 cells __default__App_option_Z) = (Some ((Znth k_2 active (0 : Int)))))) ” &&
  “ ((Znth i cells __default__App_option_Z) = (Some ((Znth i active (0 : Int))))) ”
  &&  (((flat_pre + (total * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg flat_pre (total + 1) (n_pre * n_pre))
  ** (intArray.full values_pre n_pre last_numbers)
  ** (((( &( "stack" ) ) + (i * sizeof(INT)))) # Int |-> ((Znth i active (0 : Int))))
  ** (intArray.mixed_missing_i ( &( "stack" ) ) i (0 : Int) 1005 cells)
  ** (intArray.seg flat_pre (0 : Int) total flat_data)
  ** (intArray.seg lengths_pre (0 : Int) (line + 1) lengths_data)
  ** (intArray.undef_seg lengths_pre (line + 1) n_pre)


structure VC_Correct : Type where
  proof_of_solver_safety_wit_1 : solver_safety_wit_1
  proof_of_solver_safety_wit_2 : solver_safety_wit_2
  proof_of_solver_safety_wit_3 : solver_safety_wit_3
  proof_of_solver_safety_wit_4 : solver_safety_wit_4
  proof_of_solver_safety_wit_5 : solver_safety_wit_5
  proof_of_solver_safety_wit_6 : solver_safety_wit_6
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
  proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1
  proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2
  proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3
  proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4
  proof_of_solver_safety_wit_7 : solver_safety_wit_7
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_2 : solver_entail_wit_2
  proof_of_solver_entail_wit_4 : solver_entail_wit_4
  proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1
  proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2
  proof_of_solver_entail_wit_6 : solver_entail_wit_6
  proof_of_solver_entail_wit_7 : solver_entail_wit_7
  proof_of_solver_entail_wit_8 : solver_entail_wit_8
  proof_of_solver_entail_wit_9 : solver_entail_wit_9
  proof_of_solver_entail_wit_10 : solver_entail_wit_10
  proof_of_solver_return_wit_1 : solver_return_wit_1

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_goal
